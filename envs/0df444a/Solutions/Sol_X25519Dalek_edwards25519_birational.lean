-- Prove2me | solution 1 for X25519Dalek.edwards25519_birational
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T09:47:47.440628+00:00
-- url     : https://prove2.me/submissions/07ddb5ec-eed1-4454-9e54-c1845585ab73

/- Port of google-deepmind/code-verification @ 8c8d371f (Apache-2.0), LibsignalBinary/Proofs/HookDischarge/CryptoX25519/Shared51/Math, plus new proofs (BirationalFull); see the explanation. -/
import Definitions.Def_X25519Dalek_Rfc7748

section
set_option autoImplicit false

namespace X25519Dalek

def sqrtM1 : Nat :=
  19681161376707505956807079304988542015446066515923890162744021073123829784752

def edZero : EdPoint := ⟨0, 1⟩

def edAdd (P Q : EdPoint) : EdPoint :=
  let x1y2 := fpMul P.x Q.y
  let y1x2 := fpMul P.y Q.x
  let y1y2 := fpMul P.y Q.y
  let x1x2 := fpMul P.x Q.x
  let dxxyy := fpMul edD (fpMul x1x2 y1y2)
  let x3 := fpMul (fpAdd x1y2 y1x2) (fpInv (fpAdd 1 dxxyy))
  let y3 := fpMul (fpAdd y1y2 x1x2) (fpInv (fpSub 1 dxxyy))
  ⟨x3, y3⟩

def edNeg (P : EdPoint) : EdPoint :=
  ⟨fpNeg P.x, P.y % p25519⟩

def edSub (P Q : EdPoint) : EdPoint :=
  edAdd P (edNeg Q)

def encodeEd (P : EdPoint) : List (BitVec 8) :=
  let y := P.y % p25519
  let sign := (P.x % p25519) % 2
  natToLeBytes 32 (y + sign * (2 ^ 255))

def recoverXEven (y : Nat) : Option Nat :=
  let y2 := fpSq y
  let u := fpSub y2 1
  let v := fpAdd (fpMul edD y2) 1
  let v3 := fpMul (fpSq v) v
  let v7 := fpMul (fpSq v3) v
  let r0 := fpMul (fpMul u v3) (fpPow (fpMul u v7) ((p25519 - 5) / 8))
  let check := fpMul v (fpSq r0)
  if check == u then
    some (if r0 % 2 == 1 then fpNeg r0 else r0)
  else if check == fpNeg u then
    let r1 := fpMul r0 sqrtM1
    some (if r1 % 2 == 1 then fpNeg r1 else r1)
  else
    none

def decodeEdDalek (bs : List (BitVec 8)) : Option EdPoint :=
  if bs.length != 32 then none
  else
    let n := leBytesToNat bs
    let yRaw := n % (2 ^ 255)
    let sign := (n / (2 ^ 255)) % 2
    let y := yRaw % p25519
    match recoverXEven y with
    | none => none
    | some xEven =>
      let x := if sign == 1 then fpNeg xEven else xEven
      some ⟨x, y⟩

end X25519Dalek
end

section
set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref

open X25519Dalek

export X25519Dalek (a24 decodeU255 MontProjPoint montDiffAddAndDouble montLadderLoop)
export X25519Dalek (x25519Ladder x25519 x25519Basepoint x25519Pubkey)
export X25519Dalek (lowOrderUs)

/-- Lift a 32-byte Montgomery $u$-coordinate and sign bit `sign ∈ {0, 1}` to an affine twisted
    Edwards point (`MontgomeryPoint::to_edwards`): decodes $u = \text{decodeU255}(\text{bs}) \bmod p$,
    rejects $u = p - 1$, computes $y = (u - 1) \cdot (u + 1)^{-1} \bmod p$, recovers $x_{\text{even}}$
    via `recoverXEven y`, and negates $x_{\text{even}}$ when `sign % 2 == 1`. -/
def montToEdwards (bs : List (BitVec 8)) (sign : Nat) : Option EdPoint :=
  let u := decodeU255 bs % p25519
  if u == p25519 - 1 then none
  else
    let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
    match recoverXEven y with
    | none => none
    | some xEven =>
      let x := if sign % 2 == 1 then fpNeg xEven else xEven
      some ⟨x, y⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
end

section
/-!
# $\mathbb{F}_p$ ($p = 2^{255} - 19$) field arithmetic, primality, and Fermat's little theorem

Arithmetic and primality proofs modulo `p25519 = 2^255 - 19`:

1. Commutative ring identities for `fpAdd`, `fpSub`, `fpNeg`, `fpMul`, `fpSq`, `fpPow`, and `fpInv`.
2. Modular exponentiation bridge `modPowLoop_eq` / `fpPow_eq_pow_mod`
   ($e < 2^{256} \implies \text{fpPow } a\, e = a^e \bmod p$).
3. Euclid's lemma (`IsPrime.dvd_mul`) and Fermat's little theorem (`IsPrime.pow_sub_one_mod`)
   on `Nat` via Freshman's dream.
4. Pocklington primality tests (`pocklington1`, `pocklington2`) and proof of
   `p25519_prime : IsPrime p25519`.
5. Multiplicative inverse (`fpMul_fpInv_cancel`), integral domain cancellation, difference of
   squares (`fpSq_eq_fpSq_iff`), Euler's non-square criterion (`euler_nonsquare`),
   `edD_nonsquare`, and `fpSq_sqrtM1`.
-/

set_option autoImplicit false


namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field

open X25519Dalek
/-! ## 1. Basic Bounds & Modular Normalization -/

theorem p25519_pos : 0 < p25519 := by unfold p25519; decide

theorem fpAdd_lt (a b : Nat) : fpAdd a b < p25519 := Nat.mod_lt _ p25519_pos
theorem fpSub_lt (a b : Nat) : fpSub a b < p25519 := Nat.mod_lt _ p25519_pos
theorem fpNeg_lt (a : Nat) : fpNeg a < p25519 := Nat.mod_lt _ p25519_pos
theorem fpMul_lt (a b : Nat) : fpMul a b < p25519 := Nat.mod_lt _ p25519_pos
theorem fpSq_lt (a : Nat) : fpSq a < p25519 := fpMul_lt a a
theorem edD_lt : edD < p25519 := by unfold edD p25519; decide
theorem sqrtM1_lt : sqrtM1 < p25519 := by unfold sqrtM1 p25519; decide

@[simp] theorem fpAdd_mod_p (a b : Nat) : fpAdd a b % p25519 = fpAdd a b :=
  Nat.mod_eq_of_lt (fpAdd_lt a b)
@[simp] theorem fpSub_mod_p (a b : Nat) : fpSub a b % p25519 = fpSub a b :=
  Nat.mod_eq_of_lt (fpSub_lt a b)
@[simp] theorem fpNeg_mod_p (a : Nat) : fpNeg a % p25519 = fpNeg a :=
  Nat.mod_eq_of_lt (fpNeg_lt a)
@[simp] theorem fpMul_mod_p (a b : Nat) : fpMul a b % p25519 = fpMul a b :=
  Nat.mod_eq_of_lt (fpMul_lt a b)
@[simp] theorem fpSq_mod_p (a : Nat) : fpSq a % p25519 = fpSq a :=
  Nat.mod_eq_of_lt (fpSq_lt a)
@[simp] theorem edD_mod_p : edD % p25519 = edD := Nat.mod_eq_of_lt edD_lt
@[simp] theorem sqrtM1_mod_p : sqrtM1 % p25519 = sqrtM1 := Nat.mod_eq_of_lt sqrtM1_lt

theorem fpMul_eq_mul_mod (a b : Nat) : fpMul a b = (a * b) % p25519 := by
  unfold fpMul; rw [← Nat.mul_mod]

theorem fpSq_eq_pow2_mod (a : Nat) : fpSq a = a ^ 2 % p25519 := by
  unfold fpSq; rw [fpMul_eq_mul_mod, Nat.pow_two]

@[simp] theorem fpAdd_mod_left (a b : Nat) : fpAdd (a % p25519) b = fpAdd a b := by
  unfold fpAdd; rw [Nat.mod_add_mod]
@[simp] theorem fpAdd_mod_right (a b : Nat) : fpAdd a (b % p25519) = fpAdd a b := by
  unfold fpAdd; rw [Nat.add_mod_mod]
@[simp] theorem fpNeg_mod (a : Nat) : fpNeg (a % p25519) = fpNeg a := by
  unfold fpNeg; rw [Nat.mod_mod]
@[simp] theorem fpSub_mod_left (a b : Nat) : fpSub (a % p25519) b = fpSub a b := by
  unfold fpSub
  have hb : b % p25519 ≤ p25519 := Nat.le_of_lt (Nat.mod_lt b p25519_pos)
  rw [Nat.add_sub_assoc hb, Nat.mod_add_mod, ← Nat.add_sub_assoc hb]
@[simp] theorem fpSub_mod_right (a b : Nat) : fpSub a (b % p25519) = fpSub a b := by
  unfold fpSub; rw [Nat.mod_mod]
@[simp] theorem fpMul_mod_left (a b : Nat) : fpMul (a % p25519) b = fpMul a b := by
  unfold fpMul; rw [Nat.mod_mod]
@[simp] theorem fpMul_mod_right (a b : Nat) : fpMul a (b % p25519) = fpMul a b := by
  unfold fpMul; rw [Nat.mod_mod]
@[simp] theorem fpSq_mod (a : Nat) : fpSq (a % p25519) = fpSq a := by
  unfold fpSq; rw [fpMul_mod_left, fpMul_mod_right]

/-! ## 2. Commutative Ring Identities on $\mathbb{F}_{p_{25519}}$ -/

theorem fpAdd_comm (a b : Nat) : fpAdd a b = fpAdd b a := by
  unfold fpAdd; rw [Nat.add_comm]

theorem fpAdd_assoc (a b c : Nat) : fpAdd (fpAdd a b) c = fpAdd a (fpAdd b c) := by
  unfold fpAdd; rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

@[simp] theorem fpAdd_zero (a : Nat) : fpAdd a 0 = a % p25519 := by
  unfold fpAdd; simp
@[simp] theorem zero_fpAdd (a : Nat) : fpAdd 0 a = a % p25519 := by
  unfold fpAdd; simp

@[simp] theorem fpNeg_zero : fpNeg 0 = 0 := by unfold fpNeg; simp

theorem fpNeg_of_mod_eq_zero {a : Nat} (h : a % p25519 = 0) : fpNeg a = 0 := by
  unfold fpNeg; rw [h, Nat.sub_zero, Nat.mod_self]

theorem fpNeg_of_mod_ne_zero {a : Nat} (h : a % p25519 ≠ 0) : fpNeg a = p25519 - a % p25519 := by
  unfold fpNeg
  have hlt : a % p25519 < p25519 := Nat.mod_lt a p25519_pos
  exact Nat.mod_eq_of_lt (by omega)

@[simp] theorem fpNeg_fpNeg (a : Nat) : fpNeg (fpNeg a) = a % p25519 := by
  have hlt : a % p25519 < p25519 := Nat.mod_lt a p25519_pos
  by_cases h0 : a % p25519 = 0
  · rw [fpNeg_of_mod_eq_zero h0, fpNeg_zero, h0]
  · have hsub_lt : p25519 - a % p25519 < p25519 := by omega
    have hsub_mod : (p25519 - a % p25519) % p25519 = p25519 - a % p25519 := Nat.mod_eq_of_lt hsub_lt
    rw [fpNeg_of_mod_ne_zero h0, fpNeg_of_mod_ne_zero (by rw [hsub_mod]; omega), hsub_mod]
    omega

theorem fpSub_eq_fpAdd_fpNeg (a b : Nat) : fpSub a b = fpAdd a (fpNeg b) := by
  rw [← fpSub_mod_right, ← fpNeg_mod]
  unfold fpSub fpAdd fpNeg
  rw [Nat.mod_mod]
  have hb : b % p25519 < p25519 := Nat.mod_lt b p25519_pos
  rw [Nat.add_mod a, Nat.mod_mod, ← Nat.add_mod, Nat.add_sub_assoc (by omega)]

@[simp] theorem fpAdd_fpNeg_self (a : Nat) : fpAdd a (fpNeg a) = 0 := by
  rw [← fpSub_eq_fpAdd_fpNeg, ← fpSub_mod_left]
  unfold fpSub
  have ha : a % p25519 < p25519 := Nat.mod_lt a p25519_pos
  rw [show a % p25519 + p25519 - a % p25519 = p25519 by omega, Nat.mod_self]

@[simp] theorem fpNeg_fpAdd_self (a : Nat) : fpAdd (fpNeg a) a = 0 := by
  rw [fpAdd_comm, fpAdd_fpNeg_self]

@[simp] theorem fpSub_self (a : Nat) : fpSub a a = 0 := by
  rw [fpSub_eq_fpAdd_fpNeg, fpAdd_fpNeg_self]

@[simp] theorem fpSub_zero (a : Nat) : fpSub a 0 = a % p25519 := by
  rw [fpSub_eq_fpAdd_fpNeg, fpNeg_zero, fpAdd_zero]

@[simp] theorem zero_fpSub (a : Nat) : fpSub 0 a = fpNeg a := by
  rw [fpSub_eq_fpAdd_fpNeg, zero_fpAdd, fpNeg_mod_p]

theorem fpMul_comm (a b : Nat) : fpMul a b = fpMul b a := by
  unfold fpMul; rw [Nat.mul_comm]

theorem fpMul_assoc (a b c : Nat) : fpMul (fpMul a b) c = fpMul a (fpMul b c) := by
  rw [fpMul_eq_mul_mod, fpMul_eq_mul_mod a (fpMul b c), fpMul_eq_mul_mod a b, fpMul_eq_mul_mod b c,
      Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

@[simp] theorem fpMul_zero (a : Nat) : fpMul a 0 = 0 := by unfold fpMul; simp
@[simp] theorem zero_fpMul (a : Nat) : fpMul 0 a = 0 := by unfold fpMul; simp
@[simp] theorem fpMul_one (a : Nat) : fpMul a 1 = a % p25519 := by
  rw [fpMul_eq_mul_mod, Nat.mul_one]
@[simp] theorem one_fpMul (a : Nat) : fpMul 1 a = a % p25519 := by
  rw [fpMul_eq_mul_mod, Nat.one_mul]

theorem fpMul_fpAdd (a b c : Nat) : fpMul a (fpAdd b c) = fpAdd (fpMul a b) (fpMul a c) := by
  unfold fpAdd
  rw [fpMul_mod_right, fpMul_eq_mul_mod a (b + c), fpMul_eq_mul_mod a b, fpMul_eq_mul_mod a c,
      Nat.mod_add_mod, Nat.add_mod_mod, ← Nat.mul_add]

theorem fpAdd_fpMul (a b c : Nat) : fpMul (fpAdd a b) c = fpAdd (fpMul a c) (fpMul b c) := by
  rw [fpMul_comm, fpMul_fpAdd, fpMul_comm c, fpMul_comm c]

theorem fpMul_fpNeg (a b : Nat) : fpMul a (fpNeg b) = fpNeg (fpMul a b) := by
  have h1 : fpAdd (fpMul a b) (fpMul a (fpNeg b)) = 0 := by
    rw [← fpMul_fpAdd, fpAdd_fpNeg_self, fpMul_zero]
  have h2 := congrArg (fpAdd (fpNeg (fpMul a b))) h1
  rw [← fpAdd_assoc, fpNeg_fpAdd_self, zero_fpAdd, fpAdd_zero, fpMul_mod_p, fpNeg_mod_p] at h2
  exact h2

theorem fpNeg_fpMul (a b : Nat) : fpMul (fpNeg a) b = fpNeg (fpMul a b) := by
  rw [fpMul_comm, fpMul_fpNeg, fpMul_comm]

theorem fpNeg_fpMul_fpNeg (a b : Nat) : fpMul (fpNeg a) (fpNeg b) = fpMul a b := by
  rw [fpMul_fpNeg, fpNeg_fpMul, fpNeg_fpNeg, fpMul_mod_p]

@[simp] theorem fpSq_zero : fpSq 0 = 0 := fpMul_zero 0
@[simp] theorem fpSq_one : fpSq 1 = 1 := by unfold fpSq; decide
@[simp] theorem fpSq_fpNeg (a : Nat) : fpSq (fpNeg a) = fpSq a := fpNeg_fpMul_fpNeg a a

/-! ## 3. Universal `Int` Bridge for $\mathbb{F}_{p_{25519}}$ Ring Identities (`fp_ring`) -/

/-! ## 4. Modular Exponentiation (`modPow` / `fpPow`) -/

private theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : (a == b) = false :=
  Bool.eq_false_iff.mpr (fun heq => h (beq_iff_eq.mp heq))

private theorem modPowLoop_eq (fuel : Nat) :
    ∀ (base exp m acc : Nat), exp < 2 ^ fuel → modPowLoop fuel base exp m acc = (acc * base ^ exp) % m := by
  induction fuel with
  | zero => intro base exp m acc hexp; (have h0 : exp = 0 := by omega); subst h0; simp [modPowLoop]
  | succ fuel ih =>
    intro base exp m acc hexp; unfold modPowLoop
    by_cases h0 : exp = 0
    · subst h0; simp
    · have hne : (exp == 0) = false := beq_false_of_ne h0
      have hdiv : exp / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hexp; omega
      rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hsq : ((base * base) % m) ^ (exp / 2) % m = base ^ (2 * (exp / 2)) % m := by
        rw [← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      rcases Nat.mod_two_eq_zero_or_one exp with heven | hodd
      · have hmod : (exp % 2 == 1) = false := by rw [heven]; rfl
        have hexp_eq : 2 * (exp / 2) = exp := by omega
        rw [hmod]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod, hsq, hexp_eq, ← Nat.mul_mod]
      · have hmod : (exp % 2 == 1) = true := by rw [hodd]; rfl
        have hexp_eq : (2 * (exp / 2)).succ = exp := by omega
        rw [hmod]; simp only [↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod ((acc * base) % m), Nat.mod_mod, hsq, ← Nat.mul_mod,
            Nat.mul_assoc acc, ← Nat.pow_succ', hexp_eq]

private theorem modPow_eq_pow_mod (base exp m : Nat) (he : exp < 2 ^ 256) :
    modPow base exp m = base ^ exp % m := by
  unfold modPow; rw [modPowLoop_eq 256 (base % m) exp m 1 he, Nat.one_mul, ← Nat.pow_mod base exp m]

private theorem fpPow_eq_pow_mod (a e : Nat) (he : e < 2 ^ 256) :
    fpPow a e = a ^ e % p25519 :=
  modPow_eq_pow_mod a e p25519 he

theorem fpPow_lt (a e : Nat) : fpPow a e < p25519 := by
  unfold fpPow modPow
  let rec loop_lt (fuel b exp acc : Nat) : modPowLoop fuel b exp p25519 acc < p25519 := by
    cases fuel with
    | zero => unfold modPowLoop; exact Nat.mod_lt _ p25519_pos
    | succ f =>
      unfold modPowLoop
      split
      · exact Nat.mod_lt _ p25519_pos
      · exact loop_lt f _ _ _
  exact loop_lt 256 _ _ _

theorem fpInv_lt (a : Nat) : fpInv a < p25519 := fpPow_lt a (p25519 - 2)

@[simp] theorem fpPow_mod_p (a e : Nat) : fpPow a e % p25519 = fpPow a e :=
  Nat.mod_eq_of_lt (fpPow_lt a e)
@[simp] theorem fpInv_mod_p (a : Nat) : fpInv a % p25519 = fpInv a :=
  Nat.mod_eq_of_lt (fpInv_lt a)

@[simp] theorem fpPow_mod_left (a e : Nat) : fpPow (a % p25519) e = fpPow a e := by
  unfold fpPow modPow; rw [Nat.mod_mod]
@[simp] theorem fpInv_mod (a : Nat) : fpInv (a % p25519) = fpInv a :=
  fpPow_mod_left a (p25519 - 2)

theorem fpInv_eq_pow_mod (a : Nat) : fpInv a = a ^ (p25519 - 2) % p25519 :=
  fpPow_eq_pow_mod a (p25519 - 2) (by unfold p25519; decide)

/-! ## 5. Primality, Euclid's Lemma, & Fermat's Little Theorem on `Nat` -/

/-- Primality predicate on `Nat`: `1 < p` and the only divisors of `p` are `1` and `p`. -/
def IsPrime (p : Nat) : Prop :=
  1 < p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

theorem IsPrime.gt_one {p : Nat} (hp : IsPrime p) : 1 < p := hp.1
theorem IsPrime.pos {p : Nat} (hp : IsPrime p) : 0 < p := Nat.lt_trans Nat.zero_lt_one hp.1

/-- Gauss's descent proof of Euclid's Lemma on `Nat`:
    for prime `p` and `a < p`, if `p ∣ a * b`, then `a = 0 ∨ p ∣ b`. -/
private theorem IsPrime.dvd_mul_of_lt {p : Nat} (hp : IsPrime p) :
    ∀ a < p, ∀ b, p ∣ a * b → a = 0 ∨ p ∣ b := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro ha b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha_pos
    · exact Or.inl rfl
    · by_cases ha1 : a = 1
      · subst ha1; rw [Nat.one_mul] at hab; exact Or.inr hab
      · have hmod_lt : p % a < a := Nat.mod_lt p ha_pos
        have hmod_ne : p % a ≠ 0 := by
          intro h0
          rcases hp.2 a (Nat.dvd_of_mod_eq_zero h0) with rfl | rfl
          · exact ha1 rfl
          · exact Nat.lt_irrefl a ha
        have hdiv_eq : (p % a) * b + (p / a) * (a * b) = p * b := by
          rw [← Nat.mul_assoc, ← Nat.add_mul, Nat.mod_add_div' p a]
        have hdvd_sum : p ∣ (p % a) * b + (p / a) * (a * b) := by
          rw [hdiv_eq]; exact Nat.dvd_mul_right p b
        have hdvd_rhs : p ∣ (p / a) * (a * b) := by
          rcases hab with ⟨k, hk⟩
          exact ⟨(p / a) * k, by rw [hk, ← Nat.mul_assoc, Nat.mul_comm (p / a) p, Nat.mul_assoc]⟩
        have hdvd_lhs : p ∣ (p % a) * b :=
          (Nat.dvd_add_iff_left hdvd_rhs).mpr hdvd_sum
        rcases ih (p % a) hmod_lt (Nat.lt_trans hmod_lt ha) b hdvd_lhs with h0 | hpb
        · exact absurd h0 hmod_ne
        · exact Or.inr hpb

/-- Euclid's Lemma: if `p` is prime and `p ∣ a * b`, then `p ∣ a ∨ p ∣ b`. -/
theorem IsPrime.dvd_mul {p : Nat} (hp : IsPrime p) {a b : Nat} (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  have heq : (a % p) * b + p * ((a / p) * b) = a * b := by
    rw [← Nat.mul_assoc p, ← Nat.add_mul, Nat.mod_add_div a p]
  have hdvd : p ∣ (a % p) * b := by
    apply (Nat.dvd_add_iff_left (Nat.dvd_mul_right p ((a / p) * b))).mpr
    rwa [heq]
  rcases hp.dvd_mul_of_lt (a % p) (Nat.mod_lt a hp.pos) b hdvd with h0 | hpb
  · exact Or.inl (Nat.dvd_of_mod_eq_zero h0)
  · exact Or.inr hpb

theorem IsPrime.mul_mod_eq_zero_iff {p : Nat} (hp : IsPrime p) (a b : Nat) :
    (a * b) % p = 0 ↔ a % p = 0 ∨ b % p = 0 := by
  rw [← Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero]
  refine ⟨hp.dvd_mul, ?_⟩
  rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
  · exact ⟨k * b, by rw [Nat.mul_assoc]⟩
  · exact ⟨a * k, by rw [← Nat.mul_assoc, Nat.mul_comm a p, Nat.mul_assoc]⟩

theorem IsPrime.pow_mod_eq_zero_iff {p : Nat} (hp : IsPrime p) (a : Nat) :
    ∀ n > 0, a ^ n % p = 0 ↔ a % p = 0
  | 1, _ => by rw [Nat.pow_one]
  | n + 2, _ => by
    rw [Nat.pow_succ, hp.mul_mod_eq_zero_iff, hp.pow_mod_eq_zero_iff a (n + 1) (by omega), or_self]

/-- Binomial coefficients $\binom{n}{k}$. -/
private def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

private theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl
private theorem choose_gt : ∀ (n k : Nat), n < k → choose n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    unfold choose
    rw [choose_gt n k (by omega), choose_gt n (k + 1) (by omega)]
private theorem choose_self : ∀ n : Nat, choose n n = 1
  | 0 => rfl
  | n + 1 => by unfold choose; rw [choose_self n, choose_gt n (n + 1) (by omega)]
private theorem choose_one_right : ∀ n : Nat, choose n 1 = n
  | 0 => rfl
  | n + 1 => by unfold choose; rw [choose_zero_right, choose_one_right n, Nat.add_comm]

/-- Absorption identity $(k + 1) \binom{n + 1}{k + 1} = (n + 1) \binom{n}{k}$. -/
private theorem succ_mul_choose_succ :
    ∀ (n k : Nat), (k + 1) * choose (n + 1) (k + 1) = (n + 1) * choose n k
  | n, 0 => by rw [Nat.one_mul, choose_one_right, choose_zero_right, Nat.mul_one]
  | 0, k + 1 => by
    change (k + 2) * (choose 0 (k + 1) + choose 0 (k + 2)) = 1 * choose 0 (k + 1)
    simp [choose]
  | n + 1, k + 1 => by
    change (k + 2) * (choose (n + 1) (k + 1) + choose (n + 1) (k + 2)) =
      (n + 2) * (choose n k + choose n (k + 1))
    have ih1 := succ_mul_choose_succ n k
    have ih2 := succ_mul_choose_succ n (k + 1)
    have hsplit : (k + 2) * (choose (n + 1) (k + 1) + choose (n + 1) (k + 2)) =
        (k + 1) * choose (n + 1) (k + 1) + choose (n + 1) (k + 1) +
        (k + 2) * choose (n + 1) (k + 2) := by
      rw [Nat.mul_add, Nat.succ_mul (k + 1)]
    have h1 : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl
    rw [hsplit, ih1, ih2, h1, Nat.mul_add (n + 2), Nat.succ_mul (n + 1), Nat.succ_mul (n + 1)]
    omega

/-- Kummer's lemma for prime $p$: $p \mid \binom{p}{k}$ for $0 < k < p$. -/
private theorem IsPrime.dvd_choose {p k : Nat} (hp : IsPrime p) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ choose p k := by
  rcases p with _ | p'
  · omega
  rcases k with _ | k'
  · omega
  have habs := succ_mul_choose_succ p' k'
  have hdvd : (p' + 1) ∣ (k' + 1) * choose (p' + 1) (k' + 1) :=
    ⟨choose p' k', habs⟩
  rcases hp.dvd_mul hdvd with hpk | hpc
  · exfalso; have := Nat.le_of_dvd (by omega) hpk; omega
  · exact hpc

/-- Partial binomial sum $\sum_{i=0}^{k} \binom{n}{i} a^i$. -/
private def binomSum (n a : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => binomSum n a k + choose n (k + 1) * a ^ (k + 1)

private theorem binomSum_succ (n a : Nat) :
    ∀ k : Nat, binomSum (n + 1) a (k + 1) = binomSum n a (k + 1) + a * binomSum n a k
  | 0 => by
    change 1 + (choose n 0 + choose n 1) * (1 * a) = (1 + choose n 1 * (1 * a)) + a * 1
    rw [choose_zero_right, Nat.one_mul, Nat.add_mul, Nat.one_mul, Nat.mul_one]
    omega
  | k + 1 => by
    unfold binomSum
    rw [binomSum_succ n a k]
    change (binomSum n a (k + 1) + a * binomSum n a k) +
        (choose n (k + 1) + choose n (k + 2)) * (a ^ (k + 1) * a) =
      (binomSum n a (k + 1) + choose n (k + 2) * (a ^ (k + 1) * a)) +
        a * (binomSum n a k + choose n (k + 1) * a ^ (k + 1))
    rw [Nat.add_mul, Nat.mul_add]
    have hmul : choose n (k + 1) * (a ^ (k + 1) * a) = a * (choose n (k + 1) * a ^ (k + 1)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (choose n (k + 1) * a ^ (k + 1)) a]
    omega

private theorem add_one_pow_eq_binomSum (a : Nat) :
    ∀ n : Nat, (a + 1) ^ n = binomSum n a n
  | 0 => rfl
  | n + 1 => by
    have hgt : binomSum n a (n + 1) = binomSum n a n := by
      change binomSum n a n + choose n (n + 1) * a ^ (n + 1) = binomSum n a n
      rw [choose_gt n (n + 1) (by omega), Nat.zero_mul, Nat.add_zero]
    rw [Nat.pow_succ, add_one_pow_eq_binomSum a n, binomSum_succ, hgt, Nat.mul_comm _ (a + 1),
        Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem binomSum_prime_lt_mod {p : Nat} (hp : IsPrime p) (a : Nat) :
    ∀ k < p, binomSum p a k % p = 1 % p
  | 0, _ => rfl
  | k + 1, hk => by
    unfold binomSum
    have hdvd : p ∣ choose p (k + 1) := hp.dvd_choose (by omega) hk
    have h0 : (choose p (k + 1) * a ^ (k + 1)) % p = 0 := by
      rw [Nat.mul_mod, Nat.mod_eq_zero_of_dvd hdvd, Nat.zero_mul, Nat.zero_mod]
    rw [Nat.add_mod, h0, Nat.add_zero, Nat.mod_mod, binomSum_prime_lt_mod hp a k (by omega)]

/-- Freshman's Dream: $(a + 1)^p \equiv a^p + 1 \pmod p$ for prime $p$. -/
theorem IsPrime.add_one_pow_mod {p : Nat} (hp : IsPrime p) (a : Nat) :
    (a + 1) ^ p % p = (a ^ p + 1) % p := by
  rw [add_one_pow_eq_binomSum]
  rcases p with _ | p'
  · exact absurd hp.gt_one (by decide)
  unfold binomSum
  rw [choose_self (p' + 1), Nat.one_mul, Nat.add_mod,
      binomSum_prime_lt_mod hp a p' (by omega), ← Nat.add_mod, Nat.add_comm 1]

/-- Fermat's Little Theorem (unreduced form): $a^p \equiv a \pmod p$ for all $a : \text{Nat}$. -/
theorem IsPrime.pow_mod_self {p : Nat} (hp : IsPrime p) : ∀ a : Nat, a ^ p % p = a % p
  | 0 => by
    rcases p with _ | p'
    · exact absurd hp.gt_one (by decide)
    rw [Nat.zero_pow (by omega)]
  | a + 1 => by
    rw [hp.add_one_pow_mod a, Nat.add_mod, hp.pow_mod_self a, ← Nat.add_mod]

private theorem IsPrime.mul_right_cancel_mod_of_le {p a b c : Nat} (hp : IsPrime p)
    (hc : c % p ≠ 0) (hle : a % p ≤ b % p) (h : (a * c) % p = (b * c) % p) :
    a % p = b % p := by
  have h1 : ((b % p - a % p) * c + (a % p) * c) % p = ((b % p) * c) % p := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hle]
  have h_eq : ((b % p) * c) % p = ((a % p) * c) % p := by
    rw [Nat.mod_mul_mod, ← h, ← Nat.mod_mul_mod]
  rw [h_eq] at h1
  have hdvd : p ∣ (b % p - a % p) * c := by
    have hdiv1 := Nat.div_add_mod ((b % p - a % p) * c + (a % p) * c) p
    have hdiv2 := Nat.div_add_mod ((a % p) * c) p
    have h2 : (b % p - a % p) * c =
        p * (((b % p - a % p) * c + (a % p) * c) / p - ((a % p) * c) / p) := by
      rw [Nat.mul_sub_left_distrib]; omega
    exact ⟨_, h2⟩
  rcases (hp.mul_mod_eq_zero_iff _ _).mp (Nat.mod_eq_zero_of_dvd hdvd) with h0 | h0
  · have hlt : b % p - a % p < p := Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt b hp.pos)
    rw [Nat.mod_eq_of_lt hlt] at h0; omega
  · exact absurd h0 hc

/-- Fermat's little theorem: if $p$ is prime and $a \bmod p \ne 0$, then $a^{p - 1} \bmod p = 1$. -/
theorem IsPrime.pow_sub_one_mod {p : Nat} (hp : IsPrime p) {a : Nat} (ha : a % p ≠ 0) :
    a ^ (p - 1) % p = 1 := by
  have hpow : (a ^ (p - 1) * a) % p = (1 * a) % p := by
    rw [← Nat.pow_succ, show (p - 1).succ = p by have := hp.gt_one; omega,
        hp.pow_mod_self a, Nat.one_mul]
  have hp1 : 1 % p = 1 := Nat.mod_eq_of_lt hp.gt_one
  refine (?_ : a ^ (p - 1) % p = 1 % p).trans hp1
  by_cases hle : a ^ (p - 1) % p ≤ 1 % p
  · exact hp.mul_right_cancel_mod_of_le ha hle hpow
  · exact (hp.mul_right_cancel_mod_of_le ha (by omega) hpow.symm).symm

/-! ## 6. Pocklington Primality Certificate & Proof of `IsPrime p25519` -/

/-- Every composite number $n > 1$ has a prime divisor $p$ with $p^2 \le n$. -/
private theorem exists_prime_dvd_sq_le :
    ∀ n : Nat, 1 < n → ¬ IsPrime n → ∃ p : Nat, IsPrime p ∧ p ∣ n ∧ p * p ≤ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn1 hnp
    have hex : ∃ d : Nat, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
      apply Classical.byContradiction
      intro hno
      apply hnp
      refine ⟨hn1, fun d hd => Classical.byContradiction fun hne => ?_⟩
      exact hno ⟨d, hd, fun h1 => hne (Or.inl h1), fun hn => hne (Or.inr hn)⟩
    rcases hex with ⟨d, ⟨q, hnq⟩, hd1, hdn⟩
    have hd_pos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | hpos
      · rw [Nat.zero_mul] at hnq; omega
      · exact hpos
    have hq_pos : 0 < q := by
      rcases Nat.eq_zero_or_pos q with rfl | hpos
      · rw [Nat.mul_zero] at hnq; omega
      · exact hpos
    have hd_gt1 : 1 < d := by omega
    have hq_gt1 : 1 < q := by
      rcases Nat.eq_or_lt_of_le (show 1 ≤ q by omega) with rfl | hlt
      · rw [Nat.mul_one] at hnq; exact absurd hnq.symm hdn
      · exact hlt
    have h_min : d * d ≤ n ∨ q * q ≤ n := by
      by_cases hle : d ≤ q
      · left; rw [hnq]; exact Nat.mul_le_mul_left d hle
      · have hle' : q ≤ d := by omega
        right; rw [hnq]; exact Nat.mul_le_mul_right q hle'
    have finish_factor (m : Nat) (hm1 : 1 < m) (hmn : m < n) (hmd : m ∣ n) (hmsq : m * m ≤ n) :
        ∃ p : Nat, IsPrime p ∧ p ∣ n ∧ p * p ≤ n := by
      by_cases hmp : IsPrime m
      · exact ⟨m, hmp, hmd, hmsq⟩
      · rcases ih m hmn hm1 hmp with ⟨p, hp, hpm, hpsq⟩
        have hpm_le : p ≤ m := Nat.le_of_dvd (by omega) hpm
        have hpsq_m : p * p ≤ m * m := Nat.mul_le_mul hpm_le hpm_le
        exact ⟨p, hp, Nat.dvd_trans hpm hmd, Nat.le_trans hpsq_m hmsq⟩
    rcases h_min with hdsq | hqsq
    · have hdn_lt : d < n := by
        rw [hnq]
        calc d = d * 1 := (Nat.mul_one d).symm
          _ < d * q := Nat.mul_lt_mul_of_pos_left hq_gt1 hd_pos
      exact finish_factor d hd_gt1 hdn_lt ⟨q, hnq⟩ hdsq
    · have hqn_lt : q < n := by
        rw [hnq]
        calc q = 1 * q := (Nat.one_mul q).symm
          _ < d * q := Nat.mul_lt_mul_of_pos_right hd_gt1 hq_pos
      exact finish_factor q hq_gt1 hqn_lt ⟨d, by rw [hnq, Nat.mul_comm]⟩ hqsq

/-- Order-GCD lemma: if $b^x \equiv 1 \pmod p$ and $b^y \equiv 1 \pmod p$, then
    $b^{\gcd(x, y)} \equiv 1 \pmod p$. -/
private theorem pow_mod_eq_one_gcd (b p : Nat) :
    ∀ x y : Nat, b ^ x % p = 1 % p → b ^ y % p = 1 % p → b ^ (Nat.gcd x y) % p = 1 % p := by
  intro x y
  induction x, y using Nat.gcd.induction with
  | H0 y => intro _ hy; rwa [Nat.gcd_zero_left]
  | H1 x y hx ih =>
    intro hbx hby
    rw [Nat.gcd_rec]
    apply ih _ hbx
    have hdiv : y = x * (y / x) + y % x := (Nat.div_add_mod y x).symm
    have hpow : b ^ y % p = ((b ^ x) ^ (y / x) * b ^ (y % x)) % p := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdiv]
    have h1 : (b ^ x) ^ (y / x) % p = 1 % p := by
      rw [Nat.pow_mod, hbx, ← Nat.pow_mod, Nat.one_pow]
    rw [hpow, Nat.mul_mod, h1, ← Nat.mul_mod, Nat.one_mul] at hby
    exact hby

/-- Pocklington single-prime divisor lemma: if `q` is prime, `q ∣ n - 1`,
    `modPow a (n - 1) n = 1`, and `Nat.gcd (modPow a ((n - 1) / q) n + n - 1) n = 1`,
    then for every prime divisor `p` of `n`, `q ∣ p - 1`. -/
private theorem pocklington_dvd_sub_one {n q a p : Nat}
    (hq : IsPrime q) (hq_dvd : (n - 1) % q = 0) (hn_lt : n - 1 < 2 ^ 256)
    (hfermat : modPow a (n - 1) n = 1)
    (hgcd : Nat.gcd (modPow a ((n - 1) / q) n + n - 1) n = 1)
    (hp : IsPrime p) (hp_dvd : p ∣ n) : q ∣ p - 1 := by
  have hp1 : 1 % p = 1 := Nat.mod_eq_of_lt hp.gt_one
  have hdiv_lt : (n - 1) / q < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn_lt
  have hfermat' : a ^ (n - 1) % n = 1 := by rw [← modPow_eq_pow_mod a (n - 1) n hn_lt, hfermat]
  let b := a ^ ((n - 1) / q)
  have hbq_eq : b ^ q = a ^ (n - 1) := by
    dsimp [b]; rw [← Nat.pow_mul, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hq_dvd)]
  have hbq_mod : b ^ q % p = 1 % p := by
    rw [hbq_eq, ← Nat.mod_mod_of_dvd _ hp_dvd, hfermat']
  have hb_ne0 : b % p ≠ 0 := by
    intro h0
    have : b ^ q % p = 0 := (hp.pow_mod_eq_zero_iff b q hq.pos).mpr h0
    rw [hbq_mod, hp1] at this; exact absurd this (by decide)
  have hbp1 : b ^ (p - 1) % p = 1 % p := by
    rw [hp1]; exact hp.pow_sub_one_mod hb_ne0
  have hbgcd : b ^ (Nat.gcd q (p - 1)) % p = 1 % p :=
    pow_mod_eq_one_gcd b p q (p - 1) hbq_mod hbp1
  rcases hq.2 (Nat.gcd q (p - 1)) (Nat.gcd_dvd_left q (p - 1)) with hgcd1 | hgcdq
  · exfalso
    rw [hgcd1, Nat.pow_one, hp1] at hbgcd
    let r := modPow a ((n - 1) / q) n
    have hr_eq : r = b % n := modPow_eq_pow_mod a ((n - 1) / q) n hdiv_lt
    have hr_mod : r % p = 1 := by rw [hr_eq, Nat.mod_mod_of_dvd _ hp_dvd, hbgcd]
    have hr_ne0 : r ≠ 0 := by intro h0; rw [h0, Nat.zero_mod] at hr_mod; exact absurd hr_mod (by decide)
    have hp_dvd_rn : p ∣ r + n - 1 := by
      rcases hp_dvd with ⟨k, rfl⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      have h1 : (r + p * k) % p = 1 := by rw [Nat.add_mul_mod_self_left, hr_mod]
      have hdiv := Nat.div_add_mod (r + p * k) p
      rw [h1] at hdiv
      have h2 : r + p * k - 1 = p * ((r + p * k) / p) := by omega
      rw [h2, Nat.mul_mod_right]
    have hp_dvd_one : p ∣ 1 := hgcd ▸ Nat.dvd_gcd hp_dvd_rn hp_dvd
    exact absurd (Nat.le_of_dvd Nat.one_pos hp_dvd_one) (by have := hp.gt_one; omega)
  · rw [← hgcdq]; exact Nat.gcd_dvd_right q (p - 1)

/-- Computable 1-prime Pocklington certificate check. -/
def checkPock1 (n q a : Nat) : Bool :=
  decide (1 < n) && decide (n - 1 < 2 ^ 256) &&
  ((n - 1) % q == 0) && decide (n < q * q) &&
  (modPow a (n - 1) n == 1) &&
  (Nat.gcd (modPow a ((n - 1) / q) n + n - 1) n == 1)

/-- 1-prime Pocklington primality theorem. -/
theorem pocklington1 {n q a : Nat} (hq : IsPrime q) (hchk : checkPock1 n q a = true) :
    IsPrime n := by
  unfold checkPock1 at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨hn1, hn_lt⟩, hq_dvd⟩, hnq2⟩, hfermat⟩, hgcd⟩
  apply Classical.byContradiction
  intro hnp
  rcases exists_prime_dvd_sq_le n hn1 hnp with ⟨p, hp, hp_dvd, hpsq⟩
  have hq_dvd_p1 : q ∣ p - 1 := pocklington_dvd_sub_one hq hq_dvd hn_lt hfermat hgcd hp hp_dvd
  have hqp : q < p := by
    have hp_gt1 := hp.gt_one
    have hle := Nat.le_of_dvd (by omega) hq_dvd_p1
    omega
  have hq2_lt_p2 : q * q < p * p := Nat.mul_lt_mul_of_lt_of_lt hqp hqp
  omega

/-- Computable 2-prime Pocklington certificate check. -/
def checkPock2 (n q1 q2 a : Nat) : Bool :=
  decide (1 < n) && decide (n - 1 < 2 ^ 256) && decide (q2 < q1) &&
  ((n - 1) % q1 == 0) && ((n - 1) % q2 == 0) &&
  decide (n < (q1 * q2) * (q1 * q2)) &&
  (modPow a (n - 1) n == 1) &&
  (Nat.gcd (modPow a ((n - 1) / q1) n + n - 1) n == 1) &&
  (Nat.gcd (modPow a ((n - 1) / q2) n + n - 1) n == 1)

/-- 2-prime Pocklington primality theorem. -/
theorem pocklington2 {n q1 q2 a : Nat} (hq1 : IsPrime q1) (hq2 : IsPrime q2)
    (hchk : checkPock2 n q1 q2 a = true) : IsPrime n := by
  unfold checkPock2 at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨hn1, hn_lt⟩, hq21⟩, hq1_dvd⟩, hq2_dvd⟩, hnq12⟩, hfermat⟩, hgcd1⟩, hgcd2⟩
  apply Classical.byContradiction
  intro hnp
  rcases exists_prime_dvd_sq_le n hn1 hnp with ⟨p, hp, hp_dvd, hpsq⟩
  have hd1 : q1 ∣ p - 1 := pocklington_dvd_sub_one hq1 hq1_dvd hn_lt hfermat hgcd1 hp hp_dvd
  have hd2 : q2 ∣ p - 1 := pocklington_dvd_sub_one hq2 hq2_dvd hn_lt hfermat hgcd2 hp hp_dvd
  rcases hd2 with ⟨k, hk⟩
  have hq1_dvd_prod : q1 ∣ q2 * k := hk ▸ hd1
  rcases hq1.dvd_mul hq1_dvd_prod with hq1_q2 | ⟨m, rfl⟩
  · have := Nat.le_of_dvd hq2.pos hq1_q2; omega
  · have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · rw [Nat.mul_zero, Nat.mul_zero] at hk; have := hp.gt_one; omega
      · exact hpos
    have hq12_le : q1 * q2 ≤ p - 1 := by
      rw [hk, ← Nat.mul_assoc, Nat.mul_comm q2 q1]
      exact Nat.le_mul_of_pos_right (q1 * q2) hm_pos
    have hq12_lt_p : q1 * q2 < p := by have := hp.gt_one; omega
    have hsq_lt : (q1 * q2) * (q1 * q2) < p * p := Nat.mul_lt_mul_of_lt_of_lt hq12_lt_p hq12_lt_p
    omega

/-- Trial division primality check for small primes $n < B^2$. -/
def checkSmallPrime (n B : Nat) : Bool :=
  decide (1 < n) && decide (n < B * B) &&
  (List.range' 2 (B - 2)).all (fun k => n % k != 0)

theorem smallPrime_of_check {n B : Nat} (h : checkSmallPrime n B = true) : IsPrime n := by
  unfold checkSmallPrime at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range',
    bne_iff_ne, ne_eq] at h
  rcases h with ⟨⟨hn1, hnB⟩, hall⟩
  apply Classical.byContradiction
  intro hnp
  rcases exists_prime_dvd_sq_le n hn1 hnp with ⟨p, hp, hp_dvd, hpsq⟩
  have hp_lt_B : p < B := by
    apply Classical.byContradiction
    intro hge
    have hB_le : B ≤ p := by omega
    have hB2 : B * B ≤ p * p := Nat.mul_le_mul hB_le hB_le
    omega
  have hp_ge2 : 2 ≤ p := hp.gt_one
  exact hall p ⟨p - 2, by omega, by omega⟩ (Nat.mod_eq_zero_of_dvd hp_dvd)

private theorem prime_97 : IsPrime 97 := smallPrime_of_check (B := 10) (by decide)
private theorem prime_103 : IsPrime 103 := smallPrime_of_check (B := 11) (by decide)
private theorem prime_127 : IsPrime 127 := smallPrime_of_check (B := 12) (by decide)
private theorem prime_419 : IsPrime 419 := smallPrime_of_check (B := 21) (by decide)
private theorem prime_991 : IsPrime 991 := smallPrime_of_check (B := 32) (by decide)
private theorem prime_1723 : IsPrime 1723 := smallPrime_of_check (B := 42) (by decide)
private theorem prime_4153 : IsPrime 4153 := smallPrime_of_check (B := 65) (by decide)

set_option maxRecDepth 20000 in
private theorem prime_430751 : IsPrime 430751 :=
  pocklington1 prime_1723 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_31757755568855353 : IsPrime 31757755568855353 :=
  pocklington2 prime_430751 prime_4153 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_569003 : IsPrime 569003 :=
  pocklington2 prime_419 prime_97 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_2773320623 : IsPrime 2773320623 :=
  pocklington1 prime_569003 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_72106336199 : IsPrime 72106336199 :=
  pocklington1 prime_2773320623 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_8574133 : IsPrime 8574133 :=
  pocklington2 prime_991 prime_103 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_1919519569386763 : IsPrime 1919519569386763 :=
  pocklington2 prime_8574133 prime_127 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_75445702479781427272750846543864801 :
    IsPrime 75445702479781427272750846543864801 :=
  pocklington2 prime_1919519569386763 prime_72106336199 (a := 2) (by decide)
set_option maxRecDepth 20000 in
private theorem prime_p25519_q1 :
    IsPrime 74058212732561358302231226437062788676166966415465897661863160754340907 :=
  pocklington2 prime_75445702479781427272750846543864801 prime_31757755568855353 (a := 2) (by decide)

set_option maxRecDepth 20000 in
/-- Primality of $p_{25519} = 2^{255} - 19$, proved via Pocklington's test. -/
theorem p25519_prime : IsPrime p25519 :=
  pocklington1 prime_p25519_q1 (a := 2) (by unfold p25519; decide)

/-! ## 7. Field Inversion, Cancellation, & Euler's Criterion in $\mathbb{F}_{p_{25519}}$ -/

theorem pow_p25519_sub_one_mod {a : Nat} (ha : a % p25519 ≠ 0) :
    a ^ (p25519 - 1) % p25519 = 1 :=
  p25519_prime.pow_sub_one_mod ha

set_option maxRecDepth 20000 in
@[simp] theorem fpInv_zero : fpInv 0 = 0 := by unfold fpInv fpPow modPow p25519; decide
set_option maxRecDepth 20000 in
@[simp] theorem fpInv_one : fpInv 1 = 1 := by unfold fpInv fpPow modPow p25519; decide

/-- Multiplicative inverse in $\mathbb{F}_{p_{25519}}$: `a * a^(p - 2) ≡ 1 (mod p)` for `a % p ≠ 0`. -/
theorem fpMul_fpInv_cancel {a : Nat} (ha : a % p25519 ≠ 0) : fpMul a (fpInv a) = 1 := by
  rw [fpMul_comm, fpMul_eq_mul_mod, fpInv_eq_pow_mod, Nat.mod_mul_mod, ← Nat.pow_succ,
      show (p25519 - 2).succ = p25519 - 1 by unfold p25519; decide]
  exact pow_p25519_sub_one_mod ha

theorem fpMul_cancel_right {a b c : Nat} (hc : c % p25519 ≠ 0) :
    fpMul a c = fpMul b c ↔ a % p25519 = b % p25519 := by
  constructor
  · intro h
    have h1 := congrArg (fun x => fpMul x (fpInv c)) h
    rw [fpMul_assoc, fpMul_assoc, fpMul_fpInv_cancel hc, fpMul_one, fpMul_one] at h1
    exact h1
  · intro h; rw [← fpMul_mod_left a, ← fpMul_mod_left b, h]

theorem fpMul_cancel_left {a b c : Nat} (ha : a % p25519 ≠ 0) :
    fpMul a b = fpMul a c ↔ b % p25519 = c % p25519 := by
  rw [fpMul_comm a b, fpMul_comm a c, fpMul_cancel_right ha]

theorem fpInv_eq_of_fpMul_eq_one {a b : Nat} (h : fpMul a b = 1) :
    fpInv a = b % p25519 := by
  have ha : a % p25519 ≠ 0 := by
    intro h0; rw [← fpMul_mod_left, h0, zero_fpMul] at h; exact absurd h (by decide)
  have h1 : fpMul a (fpInv a) = fpMul a b := by rw [fpMul_fpInv_cancel ha, h]
  rw [← (fpMul_cancel_left ha).mp h1, fpInv_mod_p]

/-- Euler's non-square criterion: if $d^{(p - 1)/2} \equiv p - 1 \pmod p$, then $d$ has no
    square root in $\mathbb{F}_p$. -/
theorem euler_nonsquare {d : Nat} (hd : fpPow d ((p25519 - 1) / 2) = p25519 - 1) :
    ¬ ∃ r : Nat, fpSq r = d % p25519 := by
  rintro ⟨r, hr⟩
  have he_lt : (p25519 - 1) / 2 < 2 ^ 256 := by unfold p25519; decide
  have hmul2 : 2 * ((p25519 - 1) / 2) = p25519 - 1 := by unfold p25519; decide
  rw [← fpPow_mod_left d, ← hr, fpPow_eq_pow_mod _ _ he_lt, fpSq_eq_pow2_mod,
      ← Nat.pow_mod, ← Nat.pow_mul, hmul2] at hd
  by_cases hr0 : r % p25519 = 0
  · have h0 : r ^ (p25519 - 1) % p25519 = 0 :=
      (p25519_prime.pow_mod_eq_zero_iff r (p25519 - 1) (by unfold p25519; decide)).mpr hr0
    rw [h0] at hd; revert hd; unfold p25519; decide
  · rw [pow_p25519_sub_one_mod hr0] at hd; revert hd; unfold p25519; decide

set_option maxRecDepth 20000 in
/-- `edD` is a non-square in $\mathbb{F}_{p_{25519}}$ (`edD^((p-1)/2) = p - 1`). -/
theorem edD_euler : fpPow edD ((p25519 - 1) / 2) = p25519 - 1 := by
  unfold fpPow modPow edD p25519; decide

theorem edD_nonsquare : ¬ ∃ r : Nat, fpSq r = edD := by
  rw [← edD_mod_p]; exact euler_nonsquare edD_euler

theorem fpSq_sqrtM1_eq_fpNeg_one : fpSq sqrtM1 = fpNeg 1 := by
  unfold fpSq fpMul fpNeg sqrtM1 p25519; decide

/-! ## 8. Non-Vanishing Twisted Edwards Denominators & `recoverXEven` Correctness -/

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field
end

section
/-!
# Twisted Edwards Curve Completeness, Group Laws, & Extended Coordinates (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards`)

Pure `0-sorry` mathematical proofs for the Ed25519 twisted Edwards curve
$-x^2 + y^2 \equiv 1 + d x^2 y^2 \pmod{p_{25519}}$ (`X25519Dalek.Spec.Curve25519`):
1. Prime field type `Fp` ($\mathbb{F}_{p_{25519}}$) equipped with `Lean.Grind.CommRing` and
   `Lean.Grind.Field` instances.
2. Completeness of twisted Edwards addition (`edAdd_denom_add_ne_zero` and `edAdd_denom_sub_ne_zero`)
   for all curve points `edOnCurve P = true`, `edOnCurve Q = true`, deduced from `edD_nonsquare`.
3. Curve closure and abelian group laws (`edOnCurve_edZero`, `edOnCurve_edBasepoint`,
   `edOnCurve_edNeg`, `edOnCurve_edAdd`, `edAdd_comm`, `edAdd_edZero`, `edZero_edAdd`,
   `edAdd_edNeg_self`, `edNeg_edAdd_self`, `edAdd_assoc`, `edSub_eq_iff_eq_edAdd`).
4. Homogeneous extended coordinate validity (`EdExtValid`), equivalence of `edExtAdd` with
   `edAdd` (`edExtAdd_toAffine`, `edExtValid_edExtAdd`), and `edSmul` homomorphism laws
   (`edSmul_eq_edNatSmul`, `edNatSmul_add`, `edNatSmul_mul`, `edSmul_edOrderL_edBasepoint`).
-/

set_option autoImplicit false


namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards

open X25519Dalek
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field
attribute [local irreducible] fpInv

/-! ## 1. Prime Field Type `Fp` ($\mathbb{F}_{p_{25519}}$) with `Lean.Grind.Field` Instance -/

structure Fp where
  val : Nat
  isLt : val < p25519
  deriving DecidableEq

@[ext] theorem Fp.ext {a b : Fp} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

def Fp.ofNat (n : Nat) : Fp := ⟨n % p25519, Nat.mod_lt n p25519_pos⟩

@[simp] theorem Fp.val_ofNat (n : Nat) : (Fp.ofNat n).val = n % p25519 := rfl

@[simp] theorem Fp.ofNat_val (a : Fp) : Fp.ofNat a.val = a := by
  ext; exact Nat.mod_eq_of_lt a.isLt

@[simp] theorem Fp.val_mod (a : Fp) : a.val % p25519 = a.val :=
  Nat.mod_eq_of_lt a.isLt

@[simp] theorem Fp.ofNat_mod (n : Nat) : Fp.ofNat (n % p25519) = Fp.ofNat n := by
  ext; exact Nat.mod_mod n p25519

theorem Fp.ofNat_eq_iff (a b : Nat) : Fp.ofNat a = Fp.ofNat b ↔ a % p25519 = b % p25519 :=
  ⟨fun h => congrArg Fp.val h, fun h => Fp.ext h⟩

theorem Fp.eq_of_ofNat_eq {a b : Nat} (ha : a < p25519) (hb : b < p25519)
    (h : Fp.ofNat a = Fp.ofNat b) : a = b := by
  have h1 := congrArg Fp.val h
  dsimp only [Fp.val_ofNat] at h1
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1

instance : Add Fp where
  add a b := ⟨fpAdd a.val b.val, fpAdd_lt a.val b.val⟩

instance : Sub Fp where
  sub a b := ⟨fpSub a.val b.val, fpSub_lt a.val b.val⟩

instance : Neg Fp where
  neg a := ⟨fpNeg a.val, fpNeg_lt a.val⟩

instance : Mul Fp where
  mul a b := ⟨fpMul a.val b.val, fpMul_lt a.val b.val⟩

instance : Inv Fp where
  inv a := ⟨fpInv a.val, fpInv_lt a.val⟩

instance : Div Fp where
  div a b := a * b⁻¹

instance (n : Nat) : OfNat Fp n where
  ofNat := Fp.ofNat n

instance : NatCast Fp where
  natCast := Fp.ofNat

instance : IntCast Fp where
  intCast i := if i ≥ 0 then Fp.ofNat i.toNat else -Fp.ofNat (-i).toNat

instance : SMul Nat Fp where
  smul n a := Fp.ofNat n * a

instance : SMul Int Fp where
  smul i a := (Int.cast i : Fp) * a

def Fp.npow (a : Fp) : Nat → Fp
  | 0 => 1
  | n + 1 => Fp.npow a n * a

instance : HPow Fp Nat Fp where
  hPow := Fp.npow

def Fp.zpow (a : Fp) : Int → Fp
  | .ofNat n => a ^ n
  | .negSucc n => (a ^ (n + 1))⁻¹

instance : HPow Fp Int Fp where
  hPow := Fp.zpow

@[simp] theorem Fp.val_zero : (0 : Fp).val = 0 := rfl
@[simp] theorem Fp.val_one : (1 : Fp).val = 1 := by change 1 % p25519 = 1; unfold p25519; decide
@[simp] theorem Fp.val_add (a b : Fp) : (a + b).val = fpAdd a.val b.val := rfl
@[simp] theorem Fp.val_sub (a b : Fp) : (a - b).val = fpSub a.val b.val := rfl
@[simp] theorem Fp.val_neg (a : Fp) : (-a).val = fpNeg a.val := rfl
@[simp] theorem Fp.val_mul (a b : Fp) : (a * b).val = fpMul a.val b.val := rfl
@[simp] theorem Fp.val_inv (a : Fp) : (a⁻¹).val = fpInv a.val := rfl

@[simp] theorem Fp.ofNat_zero : Fp.ofNat 0 = 0 := rfl
@[simp] theorem Fp.ofNat_one : Fp.ofNat 1 = 1 := rfl
@[simp] theorem Fp.ofNat_fpAdd (a b : Nat) : Fp.ofNat (fpAdd a b) = Fp.ofNat a + Fp.ofNat b := by
  ext; simp
@[simp] theorem Fp.ofNat_fpSub (a b : Nat) : Fp.ofNat (fpSub a b) = Fp.ofNat a - Fp.ofNat b := by
  ext; simp
@[simp] theorem Fp.ofNat_fpNeg (a : Nat) : Fp.ofNat (fpNeg a) = -Fp.ofNat a := by
  ext; simp
@[simp] theorem Fp.ofNat_fpMul (a b : Nat) : Fp.ofNat (fpMul a b) = Fp.ofNat a * Fp.ofNat b := by
  ext; simp
@[simp] theorem Fp.ofNat_fpSq (a : Nat) : Fp.ofNat (fpSq a) = Fp.ofNat a * Fp.ofNat a := by
  ext; simp [fpSq]
@[simp] theorem Fp.ofNat_fpInv (a : Nat) : Fp.ofNat (fpInv a) = (Fp.ofNat a)⁻¹ := by
  ext; simp

theorem Fp.ofNat_ne_zero_iff (a : Nat) : Fp.ofNat a ≠ 0 ↔ a % p25519 ≠ 0 := by
  rw [ne_eq, ← Fp.ofNat_zero, Fp.ofNat_eq_iff, Nat.zero_mod]

instance : Lean.Grind.Semiring Fp where
  add_zero a := by ext; simp
  add_comm a b := by ext; exact fpAdd_comm a.val b.val
  add_assoc a b c := by ext; exact fpAdd_assoc a.val b.val c.val
  mul_assoc a b c := by ext; exact fpMul_assoc a.val b.val c.val
  mul_one a := by ext; simp
  one_mul a := by ext; simp
  left_distrib a b c := by ext; exact fpMul_fpAdd a.val b.val c.val
  right_distrib a b c := by ext; exact fpAdd_fpMul a.val b.val c.val
  zero_mul a := by ext; simp
  mul_zero a := by ext; simp
  pow_zero a := rfl
  pow_succ a n := rfl
  ofNat_succ a := by
    ext
    change (a + 1) % p25519 = fpAdd (a % p25519) 1
    rw [fpAdd_mod_left]; rfl
  ofNat_eq_natCast n := rfl
  nsmul_eq_natCast_mul n a := rfl

theorem Fp.intCast_neg_lemma (i : Int) : (Int.cast (-i) : Fp) = -(Int.cast i : Fp) := by
  change (if -i ≥ 0 then Fp.ofNat (-i).toNat else -Fp.ofNat (- -i).toNat) =
    -(if i ≥ 0 then Fp.ofNat i.toNat else -Fp.ofNat (-i).toNat)
  rcases Int.lt_trichotomy i 0 with hlt | rfl | hgt
  · have h1 : -i ≥ 0 := by omega
    have h2 : ¬(i ≥ 0) := by omega
    simp only [h1, h2, ↓reduceIte]
    ext; simp
  · ext; simp
  · have h1 : ¬(-i ≥ 0) := by omega
    have h2 : i ≥ 0 := by omega
    simp only [h1, h2, ↓reduceIte, Int.neg_neg]

instance : Lean.Grind.Ring Fp where
  neg_add_cancel a := by ext; exact fpNeg_fpAdd_self a.val
  sub_eq_add_neg a b := by ext; exact fpSub_eq_fpAdd_fpNeg a.val b.val
  neg_zsmul i a := by
    change (Int.cast (-i) : Fp) * a = -((Int.cast i : Fp) * a)
    rw [Fp.intCast_neg_lemma]
    ext; exact fpNeg_fpMul _ _
  zsmul_natCast_eq_nsmul n a := rfl
  intCast_ofNat n := rfl
  intCast_neg := Fp.intCast_neg_lemma

instance : Lean.Grind.CommRing Fp where
  mul_comm a b := by ext; exact fpMul_comm a.val b.val

theorem Fp.inv_inv (a : Fp) : (a⁻¹)⁻¹ = a := by
  by_cases ha : a = 0
  · subst ha; ext; simp [fpInv_zero]
  · have ha_mod : a.val % p25519 ≠ 0 := by
      rw [Fp.val_mod]; intro h0; exact ha (Fp.ext h0)
    ext
    rw [Fp.val_inv, Fp.val_inv]
    have h1 := fpInv_eq_of_fpMul_eq_one (a := fpInv a.val) (b := a.val)
      (by rw [fpMul_comm, fpMul_fpInv_cancel ha_mod])
    rw [Fp.val_mod] at h1
    exact h1

instance : Lean.Grind.Field Fp where
  div_eq_mul_inv a b := rfl
  zero_ne_one := by intro h; have := congrArg Fp.val h; revert this; decide
  inv_zero := by ext; simp [fpInv_zero]
  mul_inv_cancel {a} ha := by
    have ha_mod : a.val % p25519 ≠ 0 := by
      rw [Fp.val_mod]; intro h0; exact ha (Fp.ext h0)
    ext; simp [fpMul_fpInv_cancel ha_mod]
  zpow_zero a := rfl
  zpow_succ a n := rfl
  zpow_neg a i := by
    cases i with
    | ofNat n =>
      cases n with
      | zero =>
        change (1 : Fp) = (1 : Fp)⁻¹
        ext; simp [fpInv_one]
      | succ k => rfl
    | negSucc k =>
      change a ^ (k + 1) = ((a ^ (k + 1))⁻¹)⁻¹
      exact (Fp.inv_inv (a ^ (k + 1))).symm

theorem Fp.edD_nonsquare : ¬ ∃ r : Fp, r * r = Fp.ofNat edD := by
  rintro ⟨r, hr⟩
  have h1 := congrArg Fp.val hr
  rw [Fp.val_mul, Fp.val_ofNat, edD_mod_p] at h1
  exact LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field.edD_nonsquare ⟨r.val, h1⟩

theorem Fp.sqrtM1_sq : Fp.ofNat sqrtM1 * Fp.ofNat sqrtM1 = -1 := by
  rw [← Fp.ofNat_fpSq, fpSq_sqrtM1_eq_fpNeg_one, Fp.ofNat_fpNeg, Fp.ofNat_one]

theorem Fp.two_ne_zero : (2 : Fp) ≠ 0 := by
  intro h; have := congrArg Fp.val h; revert this; change 2 % p25519 = 0 → False; unfold p25519; decide

/-! ## 2. Twisted Edwards Curve Equation & Completeness -/

@[ext] theorem EdPoint.ext {P Q : EdPoint} (hx : P.x = Q.x) (hy : P.y = Q.y) : P = Q := by
  cases P; cases Q; cases hx; cases hy; rfl

theorem edOnCurve_iff (P : EdPoint) :
    edOnCurve P = true ↔
      P.x < p25519 ∧ P.y < p25519 ∧
      fpAdd (fpNeg (fpSq P.x)) (fpSq P.y) =
        fpAdd 1 (fpMul edD (fpMul (fpSq P.x) (fpSq P.y))) := by
  unfold edOnCurve
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc]

theorem edOnCurve_x_lt {P : EdPoint} (hP : edOnCurve P = true) : P.x < p25519 :=
  ((edOnCurve_iff P).mp hP).1

theorem edOnCurve_y_lt {P : EdPoint} (hP : edOnCurve P = true) : P.y < p25519 :=
  ((edOnCurve_iff P).mp hP).2.1

theorem edOnCurve_eq {P : EdPoint} (hP : edOnCurve P = true) :
    fpAdd (fpNeg (fpSq P.x)) (fpSq P.y) =
      fpAdd 1 (fpMul edD (fpMul (fpSq P.x) (fpSq P.y))) :=
  ((edOnCurve_iff P).mp hP).2.2

theorem edOnCurve_fp_eq {P : EdPoint} (hP : edOnCurve P = true) :
    -(Fp.ofNat P.x * Fp.ofNat P.x) + Fp.ofNat P.y * Fp.ofNat P.y =
      1 + Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat P.x) * (Fp.ofNat P.y * Fp.ofNat P.y)) := by
  have h := congrArg Fp.ofNat (edOnCurve_eq hP)
  simpa using h

theorem edOnCurve_of_fp_eq {P : EdPoint} (hx : P.x < p25519) (hy : P.y < p25519)
    (h : -(Fp.ofNat P.x * Fp.ofNat P.x) + Fp.ofNat P.y * Fp.ofNat P.y =
      1 + Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat P.x) * (Fp.ofNat P.y * Fp.ofNat P.y))) :
    edOnCurve P = true := by
  rw [edOnCurve_iff]
  refine ⟨hx, hy, Fp.eq_of_ofNat_eq (fpAdd_lt _ _) (fpAdd_lt _ _) ?_⟩
  simpa using h

@[simp] theorem edOnCurve_edZero : edOnCurve edZero = true := by
  unfold edOnCurve edZero fpAdd fpNeg fpSq fpMul edD p25519; decide

@[simp] theorem edOnCurve_edBasepoint : edOnCurve edBasepoint = true := by
  unfold edOnCurve edBasepoint fpAdd fpNeg fpSq fpMul edD p25519; decide

theorem edOnCurve_edNeg {P : EdPoint} (hP : edOnCurve P = true) :
    edOnCurve (edNeg P) = true := by
  have hfp := edOnCurve_fp_eq hP
  apply edOnCurve_of_fp_eq (fpNeg_lt P.x) (Nat.mod_lt P.y p25519_pos)
  simp only [edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod]
  grind

private theorem completeness_ring_id (d x1 y1 x2 y2 j : Fp)
    (h1 : -(x1 * x1) + y1 * y1 = 1 + d * ((x1 * x1) * (y1 * y1)))
    (h2 : -(x2 * x2) + y2 * y2 = 1 + d * ((x2 * x2) * (y2 * y2)))
    (hd : 1 + d * ((x1 * x2) * (y1 * y2)) = 0)
    (hj : j * j = -1) :
    d * ((x1 * y1 * (x2 + j * y2)) * (x1 * y1 * (x2 + j * y2))) =
      (x1 - j * y1) * (x1 - j * y1) := by
  grind

private theorem sq_div_of_mul_sq_eq {d w v : Fp}
    (h : d * (w * w) = v * v) (hw : w ≠ 0) :
    (v * w⁻¹) * (v * w⁻¹) = d := by
  grind

/-- **Twisted Edwards Completeness (`+`)**: for any two curve points $P, Q$,
    $1 + d x_1 x_2 y_1 y_2 \not\equiv 0 \pmod{p_{25519}}$. -/
theorem edAdd_denom_add_ne_zero {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    fpAdd 1 (fpMul edD (fpMul (fpMul P.x Q.x) (fpMul P.y Q.y))) ≠ 0 := by
  intro h0
  let d := Fp.ofNat edD
  let x1 := Fp.ofNat P.x
  let y1 := Fp.ofNat P.y
  let x2 := Fp.ofNat Q.x
  let y2 := Fp.ofNat Q.y
  let i := Fp.ofNat sqrtM1
  have h1 : -(x1 * x1) + y1 * y1 = 1 + d * ((x1 * x1) * (y1 * y1)) := edOnCurve_fp_eq hP
  have h2 : -(x2 * x2) + y2 * y2 = 1 + d * ((x2 * x2) * (y2 * y2)) := edOnCurve_fp_eq hQ
  have hd : 1 + d * ((x1 * x2) * (y1 * y2)) = 0 := by
    have := congrArg Fp.ofNat h0
    simpa [d, x1, y1, x2, y2] using this
  have hi : i * i = -1 := Fp.sqrtM1_sq
  have hni : (-i) * (-i) = -1 := by grind
  have h_pos := completeness_ring_id d x1 y1 x2 y2 i h1 h2 hd hi
  have h_neg := completeness_ring_id d x1 y1 x2 y2 (-i) h1 h2 hd hni
  by_cases h_diff : x1 - i * y1 = 0
  · by_cases h_sum : x1 - (-i) * y1 = 0
    · have h2x1 : (2 : Fp) * x1 = 0 := by grind
      have h2ne : (2 : Fp) ≠ 0 := Fp.two_ne_zero
      have h10 : (1 : Fp) = 0 := by grind
      exact absurd h10.symm (by decide)
    · have hw_ne : x1 * y1 * (x2 + (-i) * y2) ≠ 0 := by grind
      exact Fp.edD_nonsquare ⟨_, sq_div_of_mul_sq_eq h_neg hw_ne⟩
  · have hw_ne : x1 * y1 * (x2 + i * y2) ≠ 0 := by grind
    exact Fp.edD_nonsquare ⟨_, sq_div_of_mul_sq_eq h_pos hw_ne⟩

/-- **Twisted Edwards Completeness (`-`)**: for any two curve points $P, Q$,
    $1 - d x_1 x_2 y_1 y_2 \not\equiv 0 \pmod{p_{25519}}$. -/
theorem edAdd_denom_sub_ne_zero {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    fpSub 1 (fpMul edD (fpMul (fpMul P.x Q.x) (fpMul P.y Q.y))) ≠ 0 := by
  have hneg := edAdd_denom_add_ne_zero (edOnCurve_edNeg hP) hQ
  intro h0
  apply hneg
  apply Fp.eq_of_ofNat_eq (fpAdd_lt _ _) (by unfold p25519; decide)
  have hfp0 : Fp.ofNat (fpSub 1 (fpMul edD (fpMul (fpMul P.x Q.x) (fpMul P.y Q.y)))) = 0 := by
    rw [h0, Fp.ofNat_zero]
  simp only [edNeg, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_fpMul, Fp.ofNat_fpNeg,
    Fp.ofNat_mod, Fp.ofNat_one, Fp.ofNat_zero] at hfp0 ⊢
  grind

/-! ## 3. Twisted Edwards Abelian Group Laws on `EdPoint` -/

theorem edAdd_x_lt (P Q : EdPoint) : (edAdd P Q).x < p25519 := fpMul_lt _ _
theorem edAdd_y_lt (P Q : EdPoint) : (edAdd P Q).y < p25519 := fpMul_lt _ _

theorem edAdd_fp_x (P Q : EdPoint) :
    Fp.ofNat (edAdd P Q).x =
      (Fp.ofNat P.x * Fp.ofNat Q.y + Fp.ofNat P.y * Fp.ofNat Q.x) *
        (1 + Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)))⁻¹ := by
  unfold edAdd
  simp

theorem edAdd_fp_y (P Q : EdPoint) :
    Fp.ofNat (edAdd P Q).y =
      (Fp.ofNat P.y * Fp.ofNat Q.y + Fp.ofNat P.x * Fp.ofNat Q.x) *
        (1 - Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)))⁻¹ := by
  unfold edAdd
  simp

theorem edAdd_fp_denom_sub_ne_zero {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    (1 : Fp) - Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)) ≠ 0 := by
  intro h
  apply edAdd_denom_sub_ne_zero hP hQ
  apply Fp.eq_of_ofNat_eq (fpSub_lt _ _) (by unfold p25519; decide)
  simpa using h

theorem edAdd_comm (P Q : EdPoint) : edAdd P Q = edAdd Q P := by
  ext
  · apply Fp.eq_of_ofNat_eq (edAdd_x_lt P Q) (edAdd_x_lt Q P)
    rw [edAdd_fp_x, edAdd_fp_x]; grind
  · apply Fp.eq_of_ofNat_eq (edAdd_y_lt P Q) (edAdd_y_lt Q P)
    rw [edAdd_fp_y, edAdd_fp_y]; grind

@[simp] theorem edAdd_edZero {P : EdPoint} (hP : edOnCurve P = true) :
    edAdd P edZero = P := by
  ext
  · apply Fp.eq_of_ofNat_eq (edAdd_x_lt P edZero) (edOnCurve_x_lt hP)
    rw [edAdd_fp_x]; simp [edZero]; grind
  · apply Fp.eq_of_ofNat_eq (edAdd_y_lt P edZero) (edOnCurve_y_lt hP)
    rw [edAdd_fp_y]; simp [edZero]; grind

@[simp] theorem edZero_edAdd {P : EdPoint} (hP : edOnCurve P = true) :
    edAdd edZero P = P := by
  rw [edAdd_comm, edAdd_edZero hP]

@[simp] theorem edAdd_edNeg_self {P : EdPoint} (hP : edOnCurve P = true) :
    edAdd P (edNeg P) = edZero := by
  have h1 := edOnCurve_fp_eq hP
  have hdm := edAdd_fp_denom_sub_ne_zero hP (edOnCurve_edNeg hP)
  simp only [edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod] at hdm
  ext
  · apply Fp.eq_of_ofNat_eq (edAdd_x_lt P (edNeg P)) (by unfold edZero p25519; decide)
    rw [edAdd_fp_x]; simp [edNeg, edZero]; grind
  · apply Fp.eq_of_ofNat_eq (edAdd_y_lt P (edNeg P)) (by unfold edZero p25519; decide)
    rw [edAdd_fp_y]; simp [edNeg, edZero]; grind

@[simp] theorem edNeg_edAdd_self {P : EdPoint} (hP : edOnCurve P = true) :
    edAdd (edNeg P) P = edZero := by
  rw [edAdd_comm, edAdd_edNeg_self hP]

@[simp] theorem edSub_self {P : EdPoint} (hP : edOnCurve P = true) :
    edSub P P = edZero :=
  edAdd_edNeg_self hP

@[simp] theorem edNeg_edZero : edNeg edZero = edZero := by
  unfold edNeg edZero fpNeg p25519; decide

@[simp] theorem edNeg_edNeg {P : EdPoint} (hP : edOnCurve P = true) :
    edNeg (edNeg P) = P := by
  ext
  · dsimp only [edNeg]
    rw [fpNeg_fpNeg, Nat.mod_eq_of_lt (edOnCurve_x_lt hP)]
  · dsimp only [edNeg]
    rw [Nat.mod_mod, Nat.mod_eq_of_lt (edOnCurve_y_lt hP)]

/-! ## 4. Extended Coordinates (`EdExtPoint`) Equivalence & Completeness -/

@[simp] theorem Fp.ofNat_edD2 : Fp.ofNat edD2 = 2 * Fp.ofNat edD := by
  ext
  change edD2 % p25519 = fpMul (2 % p25519) (edD % p25519)
  unfold edD2 edD fpMul p25519
  decide

@[simp] theorem edExtToAffine_edExtZero : edExtToAffine edExtZero = edZero := by
  ext
  · change fpMul 0 (fpInv 1) = 0; simp [fpInv_one]
  · change fpMul 1 (fpInv 1) = 1; simp [fpInv_one]

@[simp] theorem edExtToAffine_edExtOfAffine {P : EdPoint} (hP : edOnCurve P = true) :
    edExtToAffine (edExtOfAffine P) = P := by
  ext
  · dsimp only [edExtOfAffine, edExtToAffine]
    rw [fpInv_one, fpMul_one, Nat.mod_mod, Nat.mod_eq_of_lt (edOnCurve_x_lt hP)]
  · dsimp only [edExtOfAffine, edExtToAffine]
    rw [fpInv_one, fpMul_one, Nat.mod_mod, Nat.mod_eq_of_lt (edOnCurve_y_lt hP)]

theorem Fp.mul_ne_zero {a b : Fp} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro hab
  have h1 : a * b * b⁻¹ = 0 * b⁻¹ := congrArg (· * b⁻¹) hab
  have h2 : a = 0 := by grind
  exact ha h2

/-! ## 5. Scalar Multiplication Homomorphism & Basepoint Order ($\ell B = \mathcal{O}$) -/

/-- Peano scalar multiplication $[n]P$ on affine twisted Edwards points for arbitrary $n \in \mathbb{N}$. -/
def edNatSmul : Nat → EdPoint → EdPoint
  | 0, _ => edZero
  | n + 1, P => edAdd P (edNatSmul n P)

@[simp] theorem edNatSmul_zero (P : EdPoint) : edNatSmul 0 P = edZero := rfl
@[simp] theorem edNatSmul_succ (n : Nat) (P : EdPoint) :
    edNatSmul (n + 1) P = edAdd P (edNatSmul n P) := rfl

@[simp] theorem edNatSmul_edZero (n : Nat) : edNatSmul n edZero = edZero := by
  induction n with
  | zero => rfl
  | succ k ih => rw [edNatSmul_succ, ih, edAdd_edZero edOnCurve_edZero]

@[simp] theorem edNatSmul_one {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul 1 P = P := by
  rw [edNatSmul_succ, edNatSmul_zero, edAdd_edZero hP]

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards
end

section
/-!
# Point Codec, Scalar Clamping, & `recoverXEven` Proofs (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec`)

Pure `0-sorry` mathematical proofs for:
1. Little-endian byte serialization (`leBytesToNat`, `natToLeBytes`) and RFC 8032 scalar clamping
   (`clampScalarBytes`, `clampScalar`).
2. Soundness of `recoverXEven` (`recoverXEven_some_props`) and twisted Edwards point compression /
   decompression round-trips (`encodeEd_length`, `decodeEdRfc_encodeEd`, `decodeEdDalek_encodeEd`,
   `decodeEdDalek_of_decodeEdRfc`, `edOnCurve_of_decodeEdDalek`, `encodeEd_of_decodeEdRfc`).
3. Pure-specification headline theorems (`ed25519VerifyDalekEqRfc8032_ok` and
   `ed25519SignVerifyRoundtrip_ok`).
-/

set_option autoImplicit false


namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec

open X25519Dalek
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards
attribute [local irreducible] fpInv fpPow

/-! ## 1. Little-Endian Byte Codec (`leBytesToNat` / `natToLeBytes`) & Scalar Clamping -/

@[simp] private theorem natToLeBytes_length (len n : Nat) :
    (natToLeBytes len n).length = len := by
  simp [natToLeBytes]

@[simp] theorem encodeEd_length (P : EdPoint) :
    (encodeEd P).length = 32 := by
  simp [encodeEd, natToLeBytes]

/-! ## 2. Soundness of `recoverXEven` and Codec Round-Trip Lemmas -/


def decodeDalekWith (recFn : Nat → Option Nat) (bs : List (BitVec 8)) : Option EdPoint :=
  if bs.length != 32 then none
  else
    let n := leBytesToNat bs
    let yRaw := n % (2 ^ 255)
    let sign := (n / (2 ^ 255)) % 2
    let y := yRaw % p25519
    decodeEdDalek.match_1 (fun _ => Option EdPoint) (recFn y)
      (fun _ => none)
      (fun xEven =>
        let x := if sign == 1 then fpNeg xEven else xEven
        some ⟨x, y⟩)

private def decodeRfcWith (recFn : Nat → Option Nat) (bs : List (BitVec 8)) : Option EdPoint :=
  if bs.length != 32 then none
  else
    let n := leBytesToNat bs
    let yRaw := n % (2 ^ 255)
    let sign := (n / (2 ^ 255)) % 2
    if yRaw >= p25519 then none
    else
      decodeEdDalek.match_1 (fun _ => Option EdPoint) (recFn yRaw)
        (fun _ => none)
        (fun xEven =>
          if xEven == 0 && sign == 1 then none
          else
            let x := if sign == 1 then fpNeg xEven else xEven
            some ⟨x, yRaw⟩)

attribute [local irreducible] decodeDalekWith decodeRfcWith recoverXEven

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec
end

section
/-!
# Montgomery–Edwards Birational Equivalence & 8-Torsion (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational`)

Pure `0-sorry` mathematical proofs connecting Montgomery Curve25519 (`Spec.X25519`) and twisted
Edwards Ed25519 (`Spec.Curve25519`, `Spec.XEdDSA`):
1. Montgomery right-hand side `montRHS`, birational map `edToMontU`, explicit square root
   `montSqrtMinusAPlus2` of $-486664 \bmod p$, rootlessness of $u^2 + 486662 u + 1 \equiv 0 \pmod p$,
   and rational birational identities over `Fp`.
2. Complete characterization of `montToEdwards`, `decodeEdDalek` bridge, and XEdDSA round-trip.
3. Full 2-, 4-, and 8-torsion characterization on $E(\mathbb{F}_p)$ (`lowOrderUs` on-curve half).
-/

set_option autoImplicit false


namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational

open X25519Dalek
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec
/-! ## 1. Montgomery Curve Definitions & Certified $\mathbb{F}_p$ Ground Facts -/

export X25519Dalek (montRHS)

/-- Quadratic factor $u^2 + 486662 u + 1 \bmod p$ of `montRHS u = u (u^2 + 486662 u + 1)`. -/
def montQuad (u : Nat) : Nat :=
  fpAdd (fpAdd (fpSq u) (fpMul 486662 u)) 1

export X25519Dalek (edToMontU)

/-- Canonical even square root $\zeta \in \mathbb{F}_p$ of $-486664 \bmod p$
    ($\zeta^2 \equiv -486664 \pmod{p_{25519}}$). -/
def montSqrtMinusAPlus2 : Nat :=
  6853475219497561581579357271197624642482790079785650197046958215289687604742

theorem montSqrtMinusAPlus2_lt : montSqrtMinusAPlus2 < p25519 := by
  unfold montSqrtMinusAPlus2 p25519; decide +kernel
theorem fpSq_montSqrtMinusAPlus2 : fpSq montSqrtMinusAPlus2 = fpNeg 486664 := by
  unfold fpSq fpMul fpNeg montSqrtMinusAPlus2 p25519; decide +kernel

section
set_option maxRecDepth 20000
theorem edToMontU_edBasepoint : edToMontU edBasepoint = 9 := by
  unfold edToMontU edBasepoint fpMul fpAdd fpSub fpInv fpPow modPow p25519; decide +kernel
@[simp] theorem edToMontU_edZero : edToMontU edZero = 0 := by
  unfold edToMontU edZero fpMul fpAdd fpSub fpInv fpPow modPow p25519; decide +kernel
end

attribute [local irreducible] fpInv fpPow

/-! ## 2. Quadratic Non-Vanishing & Rational Birational Identities over `Fp` -/

theorem montRHS_lt (u : Nat) : montRHS u < p25519 := fpAdd_lt _ _
theorem montQuad_lt (u : Nat) : montQuad u < p25519 := fpAdd_lt _ _

@[simp] theorem montRHS_mod (u : Nat) : montRHS (u % p25519) = montRHS u := by
  apply Fp.eq_of_ofNat_eq (montRHS_lt _) (montRHS_lt _); unfold montRHS; simp

@[simp] theorem montQuad_mod (u : Nat) : montQuad (u % p25519) = montQuad u := by
  apply Fp.eq_of_ofNat_eq (montQuad_lt _) (montQuad_lt _); unfold montQuad; simp

@[simp] theorem Fp.ofNat_montRHS (u : Nat) :
    Fp.ofNat (montRHS u) = Fp.ofNat u * Fp.ofNat u * Fp.ofNat u + 486662 * (Fp.ofNat u * Fp.ofNat u) + Fp.ofNat u := by
  unfold montRHS; simp only [Fp.ofNat_fpAdd, Fp.ofNat_fpMul, Fp.ofNat_fpSq]; rfl

@[simp] theorem Fp.ofNat_montQuad (u : Nat) :
    Fp.ofNat (montQuad u) = Fp.ofNat u * Fp.ofNat u + 486662 * Fp.ofNat u + 1 := by
  unfold montQuad; simp only [Fp.ofNat_fpAdd, Fp.ofNat_fpMul, Fp.ofNat_fpSq, Fp.ofNat_one]; rfl

/-! ## 3. Complete Characterization of `montToEdwards`, XEdDSA Bridge, & `decodeEdDalek` -/

attribute [local irreducible] recoverXEven

section MontLiftAux


end MontLiftAux

attribute [local irreducible] montToEdwards

/-! ## 4. Bridge to `decodeEdDalek` (`MontgomeryPoint::to_edwards`) -/

section MontLiftBodyAux


attribute [local irreducible] decodeEdDalek decodeDalekWith

end MontLiftBodyAux

/-! ## 5. XEdDSA Round-Trip Bridge & Clamped Basepoint Non-Zero -/

section
set_option maxRecDepth 20000
end

/-! ## 6. Full 2-, 4-, and 8-Torsion Characterization on $E(\mathbb{F}_p)$ -/

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational
end

section
set_option autoImplicit false

namespace X25519DalekMath.BirationalFull

open X25519Dalek
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational

theorem edD_mul_486664 : (486664 : Fp) * Fp.ofNat edD = -486660 := by
  apply LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards.Fp.ext
  change fpMul 486664 edD = fpNeg 486660
  unfold fpMul fpNeg edD p25519; decide +kernel

theorem one_add_edD_ne_zero : (1 : Fp) + Fp.ofNat edD ≠ 0 := by
  intro h; have hval := congrArg (fun a : Fp => a.val) h; revert hval
  change fpAdd 1 edD = 0 → False
  unfold fpAdd edD p25519; decide +kernel

theorem four_ne_zero : (4 : Fp) ≠ 0 := by
  intro h; have hval := congrArg (fun a : Fp => a.val) h; revert hval
  change 4 % p25519 = 0 → False; unfold p25519; decide +kernel

theorem c486664_ne_zero : (486664 : Fp) ≠ 0 := by
  intro h; have hval := congrArg (fun a : Fp => a.val) h; revert hval
  change 486664 % p25519 = 0 → False; unfold p25519; decide +kernel

/-- Cancel a nonzero factor on the left. -/
theorem cancel_left {a b c : Fp} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have : a⁻¹ * (a * b) = a⁻¹ * (a * c) := by rw [h]
  grind

theorem mul_mul_mul_inv (a b c : Fp) (ha : a ≠ 0) : a * (b * (c * a⁻¹)) = b * c := by
  grind

/-- The key identity: with `Y (u + 1) = u − 1`, the Edwards equation
`X² (1 + d Y²) = Y² − 1` is equivalent to `X² (u² + A u + 1) = −486664 u`. -/
theorem edwards_iff_quad (X Y u : Fp) (hw : u + 1 ≠ 0) (hY : Y * (u + 1) = u - 1) :
    X * X * (1 + Fp.ofNat edD * (Y * Y)) = Y * Y - 1 ↔
      X * X * (u * u + 486662 * u + 1) = -486664 * u := by
  have hD := edD_mul_486664
  have h4 := four_ne_zero
  have hc := c486664_ne_zero
  have hw2 : (u + 1) * (u + 1) ≠ 0 := Fp.mul_ne_zero hw hw
  -- multiply the Edwards form by (u+1)², then by 486664
  have e1 : (u + 1) * (u + 1) * (X * X * (1 + Fp.ofNat edD * (Y * Y))) =
      X * X * ((u + 1) * (u + 1) + Fp.ofNat edD * ((u - 1) * (u - 1))) := by
    rw [← hY]; grind
  have e2 : (u + 1) * (u + 1) * (Y * Y - 1) = -4 * u := by
    have : (u + 1) * (u + 1) * (Y * Y - 1) = (Y * (u + 1)) * (Y * (u + 1)) - (u + 1) * (u + 1) := by
      grind
    rw [this, hY]; grind
  have e3 : 486664 * ((u + 1) * (u + 1) + Fp.ofNat edD * ((u - 1) * (u - 1))) =
      4 * (u * u + 486662 * u + 1) := by
    have : 486664 * ((u + 1) * (u + 1) + Fp.ofNat edD * ((u - 1) * (u - 1))) =
        486664 * ((u + 1) * (u + 1)) + (486664 * Fp.ofNat edD) * ((u - 1) * (u - 1)) := by grind
    rw [this, hD]; grind
  constructor
  · intro h
    have h1 : X * X * ((u + 1) * (u + 1) + Fp.ofNat edD * ((u - 1) * (u - 1))) = -4 * u := by
      rw [← e1, h, e2]
    have h2 : 4 * (X * X * (u * u + 486662 * u + 1)) = 4 * (-486664 * u) := by
      have : 4 * (X * X * (u * u + 486662 * u + 1)) =
          X * X * (486664 * ((u + 1) * (u + 1) + Fp.ofNat edD * ((u - 1) * (u - 1)))) := by
        rw [e3]; grind
      rw [this]
      have : X * X * (486664 * ((u + 1) * (u + 1) + Fp.ofNat edD * ((u - 1) * (u - 1)))) =
          486664 * (X * X * ((u + 1) * (u + 1) + Fp.ofNat edD * ((u - 1) * (u - 1)))) := by grind
      rw [this, h1]; grind
    exact cancel_left h4 h2
  · intro h
    have h1 : 486664 * (X * X * ((u + 1) * (u + 1) + Fp.ofNat edD * ((u - 1) * (u - 1)))) =
        486664 * (-4 * u) := by
      have : 486664 * (X * X * ((u + 1) * (u + 1) + Fp.ofNat edD * ((u - 1) * (u - 1)))) =
          X * X * (486664 * ((u + 1) * (u + 1) + Fp.ofNat edD * ((u - 1) * (u - 1)))) := by grind
      rw [this, e3]
      have : X * X * (4 * (u * u + 486662 * u + 1)) = 4 * (X * X * (u * u + 486662 * u + 1)) := by
        grind
      rw [this, h]; grind
    have h2 := cancel_left hc h1
    apply cancel_left hw2
    rw [e1, h2, e2]

/-- Edwards equation in the form `X² (1 + d Y²) = Y² − 1`. -/
theorem edwards_form_iff (X Y : Fp) :
    -(X * X) + Y * Y = 1 + Fp.ofNat edD * ((X * X) * (Y * Y)) ↔
      X * X * (1 + Fp.ofNat edD * (Y * Y)) = Y * Y - 1 := by
  constructor <;> intro h <;> grind

theorem ofNat_ne_zero_of_lt {a : Nat} (ha : a < p25519) (h : a ≠ 0) : Fp.ofNat a ≠ 0 := by
  rw [Fp.ofNat_ne_zero_iff, Nat.mod_eq_of_lt ha]; exact h

theorem montOnCurve_iff (u v : Nat) :
    montOnCurve u v = true ↔ u < p25519 ∧ v < p25519 ∧ fpSq v = montRHS u := by
  unfold montOnCurve
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc]

theorem sq_ofNat {s : Nat} (hs : fpSq s = fpNeg 486664) : Fp.ofNat s * Fp.ofNat s = -486664 := by
  have h := congrArg Fp.ofNat hs; rw [Fp.ofNat_fpSq, Fp.ofNat_fpNeg] at h; exact h

theorem S_ne_zero {S : Fp} (hS : S * S = -486664) : S ≠ 0 := by
  intro h; rw [h] at hS
  have : (486664 : Fp) = 0 := by grind
  exact c486664_ne_zero this

/-- Edwards to Montgomery. -/
theorem ed_to_mont (s : Nat) (hs : fpSq s = fpNeg 486664) (x y : Nat)
    (hP : edOnCurve ⟨x, y⟩ = true) (hx : x ≠ 0) (hy : y ≠ 1) :
    let u := fpMul (fpAdd 1 y) (fpInv (fpSub 1 y))
    let v := fpMul s (fpMul u (fpInv x))
    montOnCurve u v = true ∧
      fpMul s (fpMul u (fpInv v)) = x ∧ fpMul (fpSub u 1) (fpInv (fpAdd u 1)) = y := by
  intro u v
  have hudef : u = fpMul (fpAdd 1 y) (fpInv (fpSub 1 y)) := rfl
  have hvdef : v = fpMul s (fpMul u (fpInv x)) := rfl
  clear_value u v
  have hxl : x < p25519 := edOnCurve_x_lt hP
  have hyl : y < p25519 := edOnCurve_y_lt hP
  have hfp := edOnCurve_fp_eq hP
  dsimp only at hfp
  have hS := sq_ofNat hs
  have hS0 := S_ne_zero hS
  have hD1 := one_add_edD_ne_zero
  have h2 := Fp.two_ne_zero
  have hX : Fp.ofNat x ≠ 0 := ofNat_ne_zero_of_lt hxl hx
  have hY1 : (1 : Fp) - Fp.ofNat y ≠ 0 := by
    intro h
    apply hy
    apply Fp.eq_of_ofNat_eq hyl (by unfold p25519; decide)
    rw [Fp.ofNat_one]; grind
  -- Fp images
  have hU : Fp.ofNat u = (1 + Fp.ofNat y) * (1 - Fp.ofNat y)⁻¹ := by
    rw [hudef]; simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_fpInv, Fp.ofNat_one]
  have hV : Fp.ofNat v = Fp.ofNat s * (Fp.ofNat u * (Fp.ofNat x)⁻¹) := by
    rw [hvdef]; simp only [Fp.ofNat_fpMul, Fp.ofNat_fpInv]
  have hUY : Fp.ofNat u * (1 - Fp.ofNat y) = 1 + Fp.ofNat y := by rw [hU]; grind
  have hYu : Fp.ofNat y * (Fp.ofNat u + 1) = Fp.ofNat u - 1 := by grind
  have hw : Fp.ofNat u + 1 ≠ 0 := by
    intro h0; rw [h0] at hYu; grind
  -- u ≠ 0 (else y = −1, and then x = 0)
  have hu0 : Fp.ofNat u ≠ 0 := by
    intro h0
    have hy1 : Fp.ofNat y = -1 := by rw [h0] at hUY; grind
    rw [hy1] at hfp
    have : Fp.ofNat x * Fp.ofNat x * (1 + Fp.ofNat edD) = 0 := by grind
    exact Fp.mul_ne_zero (Fp.mul_ne_zero hX hX) hD1 this
  have hVX : Fp.ofNat v * Fp.ofNat x = Fp.ofNat s * Fp.ofNat u := by rw [hV]; grind
  have hV0 : Fp.ofNat v ≠ 0 := by
    intro h0; rw [h0] at hVX
    exact Fp.mul_ne_zero hS0 hu0 (by grind)
  have hquad := (edwards_iff_quad (Fp.ofNat x) (Fp.ofNat y) (Fp.ofNat u) hw hYu).1
    ((edwards_form_iff _ _).1 hfp)
  refine ⟨?_, ?_, ?_⟩
  · rw [montOnCurve_iff]
    refine ⟨by rw [hudef]; exact fpMul_lt _ _, by rw [hvdef]; exact fpMul_lt _ _, ?_⟩
    apply Fp.eq_of_ofNat_eq (fpMul_lt _ _) (montRHS_lt _)
    rw [Fp.ofNat_fpMul, Fp.ofNat_montRHS]
    apply cancel_left (Fp.mul_ne_zero hX hX)
    have : Fp.ofNat x * Fp.ofNat x * (Fp.ofNat v * Fp.ofNat v) =
        (Fp.ofNat v * Fp.ofNat x) * (Fp.ofNat v * Fp.ofNat x) := by grind
    rw [this, hVX]
    have : Fp.ofNat x * Fp.ofNat x *
        (Fp.ofNat u * Fp.ofNat u * Fp.ofNat u + 486662 * (Fp.ofNat u * Fp.ofNat u) + Fp.ofNat u) =
        Fp.ofNat u * (Fp.ofNat x * Fp.ofNat x * (Fp.ofNat u * Fp.ofNat u + 486662 * Fp.ofNat u + 1)) := by
      grind
    rw [this, hquad]
    have : Fp.ofNat s * Fp.ofNat u * (Fp.ofNat s * Fp.ofNat u) =
        (Fp.ofNat s * Fp.ofNat s) * (Fp.ofNat u * Fp.ofNat u) := by grind
    rw [this, hS]; grind
  · apply Fp.eq_of_ofNat_eq (fpMul_lt _ _) hxl
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpInv]
    apply cancel_left hV0
    have : Fp.ofNat v * (Fp.ofNat s * (Fp.ofNat u * (Fp.ofNat v)⁻¹)) = Fp.ofNat s * Fp.ofNat u :=
      mul_mul_mul_inv _ _ _ hV0
    rw [this, ← hVX] <;> try grind
  · apply Fp.eq_of_ofNat_eq (fpMul_lt _ _) hyl
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpInv, Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_one]
    apply cancel_left hw
    have : (Fp.ofNat u + 1) * ((Fp.ofNat u - 1) * (Fp.ofNat u + 1)⁻¹) = Fp.ofNat u - 1 := by grind
    rw [this, ← hYu] <;> try grind

/-- Montgomery to Edwards. -/
theorem mont_to_ed (s : Nat) (hs : fpSq s = fpNeg 486664) (u v : Nat)
    (hM : montOnCurve u v = true) (hv : v ≠ 0) (hu : u ≠ p25519 - 1) :
    let x := fpMul s (fpMul u (fpInv v))
    let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
    edOnCurve ⟨x, y⟩ = true ∧ x ≠ 0 ∧ y ≠ 1 ∧
      fpMul (fpAdd 1 y) (fpInv (fpSub 1 y)) = u ∧ fpMul s (fpMul u (fpInv x)) = v := by
  intro x y
  have hxdef : x = fpMul s (fpMul u (fpInv v)) := rfl
  have hydef : y = fpMul (fpSub u 1) (fpInv (fpAdd u 1)) := rfl
  clear_value x y
  obtain ⟨hul, hvl, hsq⟩ := (montOnCurve_iff u v).1 hM
  have hS := sq_ofNat hs
  have hS0 := S_ne_zero hS
  have h2 := Fp.two_ne_zero
  have hvfp := congrArg Fp.ofNat hsq
  rw [Fp.ofNat_fpSq, Fp.ofNat_montRHS] at hvfp
  have hV : Fp.ofNat v ≠ 0 := ofNat_ne_zero_of_lt hvl hv
  have hw : Fp.ofNat u + 1 ≠ 0 := by
    rw [← Fp.ofNat_one, ← Fp.ofNat_fpAdd, Fp.ofNat_ne_zero_iff, Nat.mod_eq_of_lt (fpAdd_lt _ _)]
    unfold fpAdd p25519 at *; omega
  have hu0 : Fp.ofNat u ≠ 0 := by
    intro h0; rw [h0] at hvfp
    exact Fp.mul_ne_zero hV hV (by grind)
  have hX : Fp.ofNat x = Fp.ofNat s * (Fp.ofNat u * (Fp.ofNat v)⁻¹) := by
    rw [hxdef]; simp only [Fp.ofNat_fpMul, Fp.ofNat_fpInv]
  have hXV : Fp.ofNat x * Fp.ofNat v = Fp.ofNat s * Fp.ofNat u := by rw [hX]; grind
  have hY : Fp.ofNat y = (Fp.ofNat u - 1) * (Fp.ofNat u + 1)⁻¹ := by
    rw [hydef]; simp only [Fp.ofNat_fpMul, Fp.ofNat_fpInv, Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_one]
  have hYu : Fp.ofNat y * (Fp.ofNat u + 1) = Fp.ofNat u - 1 := by rw [hY]; grind
  have hX0 : Fp.ofNat x ≠ 0 := by
    intro h0; rw [h0] at hXV
    exact Fp.mul_ne_zero hS0 hu0 (by grind)
  have hY1 : (1 : Fp) - Fp.ofNat y ≠ 0 := by
    intro h0
    have : Fp.ofNat y = 1 := by grind
    rw [this] at hYu
    exact h2 (by grind)
  -- the quadratic form of the Edwards equation
  have hquad : Fp.ofNat x * Fp.ofNat x * (Fp.ofNat u * Fp.ofNat u + 486662 * Fp.ofNat u + 1) =
      -486664 * Fp.ofNat u := by
    apply cancel_left (Fp.mul_ne_zero hu0 (Fp.mul_ne_zero hV hV))
    have : Fp.ofNat u * (Fp.ofNat v * Fp.ofNat v) *
        (Fp.ofNat x * Fp.ofNat x * (Fp.ofNat u * Fp.ofNat u + 486662 * Fp.ofNat u + 1)) =
        (Fp.ofNat x * Fp.ofNat v) * (Fp.ofNat x * Fp.ofNat v) *
          (Fp.ofNat u * (Fp.ofNat u * Fp.ofNat u + 486662 * Fp.ofNat u + 1)) := by grind
    rw [this, hXV]
    have e : Fp.ofNat u * (Fp.ofNat u * Fp.ofNat u + 486662 * Fp.ofNat u + 1) =
        Fp.ofNat v * Fp.ofNat v := by rw [hvfp]; grind
    rw [e]
    have : Fp.ofNat s * Fp.ofNat u * (Fp.ofNat s * Fp.ofNat u) * (Fp.ofNat v * Fp.ofNat v) =
        (Fp.ofNat s * Fp.ofNat s) * (Fp.ofNat u * (Fp.ofNat v * Fp.ofNat v)) * Fp.ofNat u := by grind
    rw [this, hS]; grind
  have hed := (edwards_form_iff _ _).2
    ((edwards_iff_quad (Fp.ofNat x) (Fp.ofNat y) (Fp.ofNat u) hw hYu).2 hquad)
  refine ⟨edOnCurve_of_fp_eq (by rw [hxdef]; exact fpMul_lt _ _) (by rw [hydef]; exact fpMul_lt _ _) hed, ?_, ?_, ?_, ?_⟩
  · intro h0; apply hX0; rw [show x = 0 from h0, Fp.ofNat_zero]
  · intro h1; apply hY1; rw [show y = 1 from h1, Fp.ofNat_one]; grind
  · apply Fp.eq_of_ofNat_eq (fpMul_lt _ _) hul
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpInv, Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_one]
    apply cancel_left hY1
    have : (1 - Fp.ofNat y) * ((1 + Fp.ofNat y) * (1 - Fp.ofNat y)⁻¹) = 1 + Fp.ofNat y := by grind
    rw [this]
    grind
  · apply Fp.eq_of_ofNat_eq (fpMul_lt _ _) hvl
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpInv]
    apply cancel_left hX0
    have : Fp.ofNat x * (Fp.ofNat s * (Fp.ofNat u * (Fp.ofNat x)⁻¹)) = Fp.ofNat s * Fp.ofNat u :=
      mul_mul_mul_inv _ _ _ hX0
    rw [this, ← hXV] <;> try grind

theorem edOnCurve_edBasepoint : edOnCurve edBasepoint = true := by
  unfold edOnCurve edBasepoint fpAdd fpNeg fpSq fpMul edD p25519; decide +kernel

theorem edwards25519_birational :
    (∃ s : Nat, s < p25519 ∧ fpSq s = fpNeg 486664) ∧
    (∀ s : Nat, fpSq s = fpNeg 486664 →
      (∀ x y : Nat, edOnCurve ⟨x, y⟩ = true → x ≠ 0 → y ≠ 1 →
        let u := fpMul (fpAdd 1 y) (fpInv (fpSub 1 y))
        let v := fpMul s (fpMul u (fpInv x))
        montOnCurve u v = true ∧
          fpMul s (fpMul u (fpInv v)) = x ∧ fpMul (fpSub u 1) (fpInv (fpAdd u 1)) = y) ∧
      (∀ u v : Nat, montOnCurve u v = true → v ≠ 0 → u ≠ p25519 - 1 →
        let x := fpMul s (fpMul u (fpInv v))
        let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
        edOnCurve ⟨x, y⟩ = true ∧ x ≠ 0 ∧ y ≠ 1 ∧
          fpMul (fpAdd 1 y) (fpInv (fpSub 1 y)) = u ∧ fpMul s (fpMul u (fpInv x)) = v)) ∧
    edOnCurve edBasepoint = true ∧ edToMontU edBasepoint = 9 :=
  ⟨⟨montSqrtMinusAPlus2, montSqrtMinusAPlus2_lt, fpSq_montSqrtMinusAPlus2⟩,
   fun s hs => ⟨ed_to_mont s hs, mont_to_ed s hs⟩,
   edOnCurve_edBasepoint, edToMontU_edBasepoint⟩

end X25519DalekMath.BirationalFull
end

open X25519Dalek in
theorem solution :
    (∃ s : Nat, s < p25519 ∧ fpSq s = fpNeg 486664) ∧
    (∀ s : Nat, fpSq s = fpNeg 486664 →
      (∀ x y : Nat, edOnCurve ⟨x, y⟩ = true → x ≠ 0 → y ≠ 1 →
        let u := fpMul (fpAdd 1 y) (fpInv (fpSub 1 y))
        let v := fpMul s (fpMul u (fpInv x))
        montOnCurve u v = true ∧
          fpMul s (fpMul u (fpInv v)) = x ∧ fpMul (fpSub u 1) (fpInv (fpAdd u 1)) = y) ∧
      (∀ u v : Nat, montOnCurve u v = true → v ≠ 0 → u ≠ p25519 - 1 →
        let x := fpMul s (fpMul u (fpInv v))
        let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
        edOnCurve ⟨x, y⟩ = true ∧ x ≠ 0 ∧ y ≠ 1 ∧
          fpMul (fpAdd 1 y) (fpInv (fpSub 1 y)) = u ∧ fpMul s (fpMul u (fpInv x)) = v)) ∧
    edOnCurve edBasepoint = true ∧ edToMontU edBasepoint = 9 :=
  X25519DalekMath.BirationalFull.edwards25519_birational
