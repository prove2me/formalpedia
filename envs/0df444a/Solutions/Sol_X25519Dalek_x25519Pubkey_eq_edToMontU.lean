-- Prove2me | solution 1 for X25519Dalek.x25519Pubkey_eq_edToMontU
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T09:52:57.810806+00:00
-- url     : https://prove2.me/submissions/01baa432-10a3-4116-9bf3-515a70d58201

/- Port of google-deepmind/code-verification @ 8c8d371f (Apache-2.0), LibsignalBinary/Proofs/HookDischarge/CryptoX25519 (Shared51/Math, MontgomeryLadder); see the explanation. -/
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

theorem edAdd_fp_denom_add_ne_zero {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    (1 : Fp) + Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)) ≠ 0 := by
  intro h
  apply edAdd_denom_add_ne_zero hP hQ
  apply Fp.eq_of_ofNat_eq (fpAdd_lt _ _) (by unfold p25519; decide)
  simpa using h

theorem edAdd_fp_denom_sub_ne_zero {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    (1 : Fp) - Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)) ≠ 0 := by
  intro h
  apply edAdd_denom_sub_ne_zero hP hQ
  apply Fp.eq_of_ofNat_eq (fpSub_lt _ _) (by unfold p25519; decide)
  simpa using h

private theorem edAdd_onCurve_ring (d x1 y1 x2 y2 : Fp)
    (h1 : -(x1 * x1) + y1 * y1 = 1 + d * ((x1 * x1) * (y1 * y1)))
    (h2 : -(x2 * x2) + y2 * y2 = 1 + d * ((x2 * x2) * (y2 * y2))) :
    let u := x1 * y2 + y1 * x2
    let v := y1 * y2 + x1 * x2
    let dp := 1 + d * ((x1 * x2) * (y1 * y2))
    let dm := 1 - d * ((x1 * x2) * (y1 * y2));
    -((u * dm) * (u * dm)) + (v * dp) * (v * dp) =
      (dp * dm) * (dp * dm) + d * ((u * u) * (v * v)) := by
  grind

theorem edOnCurve_edAdd {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    edOnCurve (edAdd P Q) = true := by
  apply edOnCurve_of_fp_eq (edAdd_x_lt P Q) (edAdd_y_lt P Q)
  have h1 := edOnCurve_fp_eq hP
  have h2 := edOnCurve_fp_eq hQ
  have hdp := edAdd_fp_denom_add_ne_zero hP hQ
  have hdm := edAdd_fp_denom_sub_ne_zero hP hQ
  have hring := edAdd_onCurve_ring (Fp.ofNat edD) (Fp.ofNat P.x) (Fp.ofNat P.y)
    (Fp.ofNat Q.x) (Fp.ofNat Q.y) h1 h2
  dsimp only at hring
  rw [edAdd_fp_x, edAdd_fp_y]
  grind

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

theorem edNeg_edAdd (P Q : EdPoint) :
    edNeg (edAdd P Q) = edAdd (edNeg P) (edNeg Q) := by
  ext
  · apply Fp.eq_of_ofNat_eq (fpNeg_lt _) (edAdd_x_lt _ _)
    rw [edAdd_fp_x]; simp [edNeg, edAdd_fp_x]; grind
  · apply Fp.eq_of_ofNat_eq (Nat.mod_lt _ p25519_pos) (edAdd_y_lt _ _)
    rw [edAdd_fp_y]; simp [edNeg, edAdd_fp_y]; grind

private theorem edAdd_assoc_x_ring (d x1 y1 x2 y2 x3 y3 : Fp)
    (h1 : d * ((x1 * x1) * (y1 * y1)) = -(x1 * x1) + y1 * y1 - 1)
    (h2 : d * ((x2 * x2) * (y2 * y2)) = -(x2 * x2) + y2 * y2 - 1)
    (h3 : d * ((x3 * x3) * (y3 * y3)) = -(x3 * x3) + y3 * y3 - 1) :
    let u12 := x1 * y2 + y1 * x2
    let v12 := y1 * y2 + x1 * x2
    let dp12 := 1 + d * ((x1 * x2) * (y1 * y2))
    let dm12 := 1 - d * ((x1 * x2) * (y1 * y2))
    let u23 := x2 * y3 + y2 * x3
    let v23 := y2 * y3 + x2 * x3
    let dp23 := 1 + d * ((x2 * x3) * (y2 * y3))
    let dm23 := 1 - d * ((x2 * x3) * (y2 * y3));
    (u12 * dm12 * y3 + v12 * dp12 * x3) * (dp23 * dm23 + d * ((x1 * u23) * (y1 * v23))) =
      (x1 * dp23 * v23 + y1 * dm23 * u23) * (dp12 * dm12 + d * ((u12 * x3) * (v12 * y3))) := by
  grind

private theorem edAdd_assoc_y_ring (d x1 y1 x2 y2 x3 y3 : Fp)
    (h1 : d * ((x1 * x1) * (y1 * y1)) = -(x1 * x1) + y1 * y1 - 1)
    (h2 : d * ((x2 * x2) * (y2 * y2)) = -(x2 * x2) + y2 * y2 - 1)
    (h3 : d * ((x3 * x3) * (y3 * y3)) = -(x3 * x3) + y3 * y3 - 1) :
    let u12 := x1 * y2 + y1 * x2
    let v12 := y1 * y2 + x1 * x2
    let dp12 := 1 + d * ((x1 * x2) * (y1 * y2))
    let dm12 := 1 - d * ((x1 * x2) * (y1 * y2))
    let u23 := x2 * y3 + y2 * x3
    let v23 := y2 * y3 + x2 * x3
    let dp23 := 1 + d * ((x2 * x3) * (y2 * y3))
    let dm23 := 1 - d * ((x2 * x3) * (y2 * y3));
    (v12 * dp12 * y3 + u12 * dm12 * x3) * (dp23 * dm23 - d * ((x1 * u23) * (y1 * v23))) =
      (y1 * dp23 * v23 + x1 * dm23 * u23) * (dp12 * dm12 - d * ((u12 * x3) * (v12 * y3))) := by
  grind

private theorem edAdd_assoc_x_clear (d u12 v12 dp12 dm12 u23 v23 dp23 dm23 x1 y1 x3 y3 : Fp)
    (hdp12 : dp12 ≠ 0) (hdm12 : dm12 ≠ 0) (hdp23 : dp23 ≠ 0) (hdm23 : dm23 ≠ 0)
    (hdp12_3 : 1 + d * (((u12 * dp12⁻¹) * x3) * ((v12 * dm12⁻¹) * y3)) ≠ 0)
    (hdp1_23 : 1 + d * ((x1 * (u23 * dp23⁻¹)) * (y1 * (v23 * dm23⁻¹))) ≠ 0)
    (hring : (u12 * dm12 * y3 + v12 * dp12 * x3) * (dp23 * dm23 + d * ((x1 * u23) * (y1 * v23))) =
      (x1 * dp23 * v23 + y1 * dm23 * u23) * (dp12 * dm12 + d * ((u12 * x3) * (v12 * y3)))) :
    ((u12 * dp12⁻¹) * y3 + (v12 * dm12⁻¹) * x3) *
        (1 + d * (((u12 * dp12⁻¹) * x3) * ((v12 * dm12⁻¹) * y3)))⁻¹ =
      (x1 * (v23 * dm23⁻¹) + y1 * (u23 * dp23⁻¹)) *
        (1 + d * ((x1 * (u23 * dp23⁻¹)) * (y1 * (v23 * dm23⁻¹))))⁻¹ := by
  grind

private theorem edAdd_assoc_y_clear (d u12 v12 dp12 dm12 u23 v23 dp23 dm23 x1 y1 x3 y3 : Fp)
    (hdp12 : dp12 ≠ 0) (hdm12 : dm12 ≠ 0) (hdp23 : dp23 ≠ 0) (hdm23 : dm23 ≠ 0)
    (hdm12_3 : 1 - d * (((u12 * dp12⁻¹) * x3) * ((v12 * dm12⁻¹) * y3)) ≠ 0)
    (hdm1_23 : 1 - d * ((x1 * (u23 * dp23⁻¹)) * (y1 * (v23 * dm23⁻¹))) ≠ 0)
    (hring : (v12 * dp12 * y3 + u12 * dm12 * x3) * (dp23 * dm23 - d * ((x1 * u23) * (y1 * v23))) =
      (y1 * dp23 * v23 + x1 * dm23 * u23) * (dp12 * dm12 - d * ((u12 * x3) * (v12 * y3)))) :
    ((v12 * dm12⁻¹) * y3 + (u12 * dp12⁻¹) * x3) *
        (1 - d * (((u12 * dp12⁻¹) * x3) * ((v12 * dm12⁻¹) * y3)))⁻¹ =
      (y1 * (v23 * dm23⁻¹) + x1 * (u23 * dp23⁻¹)) *
        (1 - d * ((x1 * (u23 * dp23⁻¹)) * (y1 * (v23 * dm23⁻¹))))⁻¹ := by
  grind

theorem edAdd_assoc {P Q R : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) (hR : edOnCurve R = true) :
    edAdd (edAdd P Q) R = edAdd P (edAdd Q R) := by
  have hPQ : edOnCurve (edAdd P Q) = true := edOnCurve_edAdd hP hQ
  have hQR : edOnCurve (edAdd Q R) = true := edOnCurve_edAdd hQ hR
  have h1 : Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat P.x) * (Fp.ofNat P.y * Fp.ofNat P.y)) =
      -(Fp.ofNat P.x * Fp.ofNat P.x) + Fp.ofNat P.y * Fp.ofNat P.y - 1 := by
    have := edOnCurve_fp_eq hP; grind
  have h2 : Fp.ofNat edD * ((Fp.ofNat Q.x * Fp.ofNat Q.x) * (Fp.ofNat Q.y * Fp.ofNat Q.y)) =
      -(Fp.ofNat Q.x * Fp.ofNat Q.x) + Fp.ofNat Q.y * Fp.ofNat Q.y - 1 := by
    have := edOnCurve_fp_eq hQ; grind
  have h3 : Fp.ofNat edD * ((Fp.ofNat R.x * Fp.ofNat R.x) * (Fp.ofNat R.y * Fp.ofNat R.y)) =
      -(Fp.ofNat R.x * Fp.ofNat R.x) + Fp.ofNat R.y * Fp.ofNat R.y - 1 := by
    have := edOnCurve_fp_eq hR; grind
  have hdp12 := edAdd_fp_denom_add_ne_zero hP hQ
  have hdm12 := edAdd_fp_denom_sub_ne_zero hP hQ
  have hdp23 := edAdd_fp_denom_add_ne_zero hQ hR
  have hdm23 := edAdd_fp_denom_sub_ne_zero hQ hR
  have hdp12_3 := edAdd_fp_denom_add_ne_zero hPQ hR
  have hdm12_3 := edAdd_fp_denom_sub_ne_zero hPQ hR
  have hdp1_23 := edAdd_fp_denom_add_ne_zero hP hQR
  have hdm1_23 := edAdd_fp_denom_sub_ne_zero hP hQR
  rw [edAdd_fp_x P Q, edAdd_fp_y P Q] at hdp12_3 hdm12_3
  rw [edAdd_fp_x Q R, edAdd_fp_y Q R] at hdp1_23 hdm1_23
  ext
  · apply Fp.eq_of_ofNat_eq (edAdd_x_lt _ _) (edAdd_x_lt _ _)
    have hx_ring := edAdd_assoc_x_ring (Fp.ofNat edD)
      (Fp.ofNat P.x) (Fp.ofNat P.y) (Fp.ofNat Q.x) (Fp.ofNat Q.y) (Fp.ofNat R.x) (Fp.ofNat R.y)
      h1 h2 h3
    rw [edAdd_fp_x (edAdd P Q) R, edAdd_fp_x P (edAdd Q R),
        edAdd_fp_x P Q, edAdd_fp_y P Q, edAdd_fp_x Q R, edAdd_fp_y Q R]
    exact edAdd_assoc_x_clear _ _ _ _ _ _ _ _ _ _ _ _ _
      hdp12 hdm12 hdp23 hdm23 hdp12_3 hdp1_23 hx_ring
  · apply Fp.eq_of_ofNat_eq (edAdd_y_lt _ _) (edAdd_y_lt _ _)
    have hy_ring := edAdd_assoc_y_ring (Fp.ofNat edD)
      (Fp.ofNat P.x) (Fp.ofNat P.y) (Fp.ofNat Q.x) (Fp.ofNat Q.y) (Fp.ofNat R.x) (Fp.ofNat R.y)
      h1 h2 h3
    rw [edAdd_fp_y (edAdd P Q) R, edAdd_fp_y P (edAdd Q R),
        edAdd_fp_x P Q, edAdd_fp_y P Q, edAdd_fp_x Q R, edAdd_fp_y Q R]
    exact edAdd_assoc_y_clear _ _ _ _ _ _ _ _ _ _ _ _ _
      hdp12 hdm12 hdp23 hdm23 hdm12_3 hdm1_23 hy_ring

/-! ## 4. Extended Coordinates (`EdExtPoint`) Equivalence & Completeness -/

@[simp] theorem Fp.ofNat_edD2 : Fp.ofNat edD2 = 2 * Fp.ofNat edD := by
  ext
  change edD2 % p25519 = fpMul (2 % p25519) (edD % p25519)
  unfold edD2 edD fpMul p25519
  decide

/-- Well-formedness invariant for extended twisted Edwards points $P = (X, Y, Z, T)$:
    $Z \not\equiv 0 \pmod p$, $T Z \equiv X Y \pmod p$, and the projected affine point
    $(X Z^{-1}, Y Z^{-1})$ lies on the curve. -/
structure EdExtValid (P : EdExtPoint) : Prop where
  z_ne_zero : Fp.ofNat P.Z ≠ 0
  tz_eq_xy : Fp.ofNat P.T * Fp.ofNat P.Z = Fp.ofNat P.X * Fp.ofNat P.Y
  on_curve : edOnCurve (edExtToAffine P) = true

theorem edExtToAffine_x_lt (P : EdExtPoint) : (edExtToAffine P).x < p25519 := fpMul_lt _ _
theorem edExtToAffine_y_lt (P : EdExtPoint) : (edExtToAffine P).y < p25519 := fpMul_lt _ _

theorem edExtToAffine_fp_x (P : EdExtPoint) :
    Fp.ofNat (edExtToAffine P).x = Fp.ofNat P.X * (Fp.ofNat P.Z)⁻¹ := by
  unfold edExtToAffine; simp

theorem edExtToAffine_fp_y (P : EdExtPoint) :
    Fp.ofNat (edExtToAffine P).y = Fp.ofNat P.Y * (Fp.ofNat P.Z)⁻¹ := by
  unfold edExtToAffine; simp

@[simp] theorem edExtToAffine_edExtZero : edExtToAffine edExtZero = edZero := by
  ext
  · change fpMul 0 (fpInv 1) = 0; simp [fpInv_one]
  · change fpMul 1 (fpInv 1) = 1; simp [fpInv_one]

theorem edExtValid_edExtZero : EdExtValid edExtZero where
  z_ne_zero := by intro h; have := congrArg Fp.val h; revert this; decide
  tz_eq_xy := by ext; simp [edExtZero]
  on_curve := by rw [edExtToAffine_edExtZero]; exact edOnCurve_edZero

@[simp] theorem edExtToAffine_edExtOfAffine {P : EdPoint} (hP : edOnCurve P = true) :
    edExtToAffine (edExtOfAffine P) = P := by
  ext
  · dsimp only [edExtOfAffine, edExtToAffine]
    rw [fpInv_one, fpMul_one, Nat.mod_mod, Nat.mod_eq_of_lt (edOnCurve_x_lt hP)]
  · dsimp only [edExtOfAffine, edExtToAffine]
    rw [fpInv_one, fpMul_one, Nat.mod_mod, Nat.mod_eq_of_lt (edOnCurve_y_lt hP)]

theorem edExtValid_edExtOfAffine {P : EdPoint} (hP : edOnCurve P = true) :
    EdExtValid (edExtOfAffine P) where
  z_ne_zero := edExtValid_edExtZero.z_ne_zero
  tz_eq_xy := by unfold edExtOfAffine; simp; grind
  on_curve := by rw [edExtToAffine_edExtOfAffine hP]; exact hP

theorem Fp.mul_ne_zero {a b : Fp} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro hab
  have h1 : a * b * b⁻¹ = 0 * b⁻¹ := congrArg (· * b⁻¹) hab
  have h2 : a = 0 := by grind
  exact ha h2

private theorem edExtAdd_z_ne_zero_ring (d X1 Y1 Z1 T1 X2 Y2 Z2 T2 x1 y1 x2 y2 : Fp)
    (h2 : (2 : Fp) ≠ 0) (hZ1 : Z1 ≠ 0) (hZ2 : Z2 ≠ 0)
    (hT1 : T1 * Z1 = X1 * Y1) (hT2 : T2 * Z2 = X2 * Y2)
    (hx1 : x1 = X1 * Z1⁻¹) (hy1 : y1 = Y1 * Z1⁻¹)
    (hx2 : x2 = X2 * Z2⁻¹) (hy2 : y2 = Y2 * Z2⁻¹)
    (hdp : 1 + d * ((x1 * x2) * (y1 * y2)) ≠ 0)
    (hdm : 1 - d * ((x1 * x2) * (y1 * y2)) ≠ 0) :
    (Z1 * (Z2 + Z2) - T1 * (2 * d * T2)) * (Z1 * (Z2 + Z2) + T1 * (2 * d * T2)) ≠ 0 := by
  have hF : Z1 * (Z2 + Z2) - T1 * (2 * d * T2) =
      2 * Z1 * Z2 * (1 - d * ((x1 * x2) * (y1 * y2))) := by grind
  have hG : Z1 * (Z2 + Z2) + T1 * (2 * d * T2) =
      2 * Z1 * Z2 * (1 + d * ((x1 * x2) * (y1 * y2))) := by grind
  rw [hF, hG]
  exact Fp.mul_ne_zero
    (Fp.mul_ne_zero (Fp.mul_ne_zero (Fp.mul_ne_zero h2 hZ1) hZ2) hdm)
    (Fp.mul_ne_zero (Fp.mul_ne_zero (Fp.mul_ne_zero h2 hZ1) hZ2) hdp)

private theorem edExtAdd_x_ring (d X1 Y1 Z1 T1 X2 Y2 Z2 T2 x1 y1 x2 y2 : Fp)
    (h2 : (2 : Fp) ≠ 0) (hZ1 : Z1 ≠ 0) (hZ2 : Z2 ≠ 0)
    (hT1 : T1 * Z1 = X1 * Y1) (hT2 : T2 * Z2 = X2 * Y2)
    (hx1 : x1 = X1 * Z1⁻¹) (hy1 : y1 = Y1 * Z1⁻¹)
    (hx2 : x2 = X2 * Z2⁻¹) (hy2 : y2 = Y2 * Z2⁻¹)
    (hdp : 1 + d * ((x1 * x2) * (y1 * y2)) ≠ 0)
    (hdm : 1 - d * ((x1 * x2) * (y1 * y2)) ≠ 0) :
    let A := (Y1 - X1) * (Y2 - X2)
    let B := (Y1 + X1) * (Y2 + X2)
    let C := T1 * (2 * d * T2)
    let D := Z1 * (Z2 + Z2)
    let E := B - A
    let F := D - C
    let G := D + C;
    (E * F) * (F * G)⁻¹ = (x1 * y2 + y1 * x2) * (1 + d * ((x1 * x2) * (y1 * y2)))⁻¹ := by
  have hFG := edExtAdd_z_ne_zero_ring d X1 Y1 Z1 T1 X2 Y2 Z2 T2 x1 y1 x2 y2
    h2 hZ1 hZ2 hT1 hT2 hx1 hy1 hx2 hy2 hdp hdm
  grind

private theorem edExtAdd_y_ring (d X1 Y1 Z1 T1 X2 Y2 Z2 T2 x1 y1 x2 y2 : Fp)
    (h2 : (2 : Fp) ≠ 0) (hZ1 : Z1 ≠ 0) (hZ2 : Z2 ≠ 0)
    (hT1 : T1 * Z1 = X1 * Y1) (hT2 : T2 * Z2 = X2 * Y2)
    (hx1 : x1 = X1 * Z1⁻¹) (hy1 : y1 = Y1 * Z1⁻¹)
    (hx2 : x2 = X2 * Z2⁻¹) (hy2 : y2 = Y2 * Z2⁻¹)
    (hdp : 1 + d * ((x1 * x2) * (y1 * y2)) ≠ 0)
    (hdm : 1 - d * ((x1 * x2) * (y1 * y2)) ≠ 0) :
    let A := (Y1 - X1) * (Y2 - X2)
    let B := (Y1 + X1) * (Y2 + X2)
    let C := T1 * (2 * d * T2)
    let D := Z1 * (Z2 + Z2)
    let F := D - C
    let G := D + C
    let H := B + A;
    (G * H) * (F * G)⁻¹ = (y1 * y2 + x1 * x2) * (1 - d * ((x1 * x2) * (y1 * y2)))⁻¹ := by
  have hFG := edExtAdd_z_ne_zero_ring d X1 Y1 Z1 T1 X2 Y2 Z2 T2 x1 y1 x2 y2
    h2 hZ1 hZ2 hT1 hT2 hx1 hy1 hx2 hy2 hdp hdm
  grind

theorem edExtAdd_toAffine {P Q : EdExtPoint}
    (hP : EdExtValid P) (hQ : EdExtValid Q) :
    edExtToAffine (edExtAdd P Q) = edAdd (edExtToAffine P) (edExtToAffine Q) := by
  have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hQ.on_curve
  have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hQ.on_curve
  ext
  · apply Fp.eq_of_ofNat_eq (edExtToAffine_x_lt _) (edAdd_x_lt _ _)
    rw [edExtToAffine_fp_x, edAdd_fp_x]
    unfold edExtAdd
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_edD2]
    exact edExtAdd_x_ring _ _ _ _ _ _ _ _ _ _ _ _ _
      Fp.two_ne_zero hP.z_ne_zero hQ.z_ne_zero hP.tz_eq_xy hQ.tz_eq_xy
      (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
      (edExtToAffine_fp_x Q) (edExtToAffine_fp_y Q) hdp hdm
  · apply Fp.eq_of_ofNat_eq (edExtToAffine_y_lt _) (edAdd_y_lt _ _)
    rw [edExtToAffine_fp_y, edAdd_fp_y]
    unfold edExtAdd
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_edD2]
    exact edExtAdd_y_ring _ _ _ _ _ _ _ _ _ _ _ _ _
      Fp.two_ne_zero hP.z_ne_zero hQ.z_ne_zero hP.tz_eq_xy hQ.tz_eq_xy
      (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
      (edExtToAffine_fp_x Q) (edExtToAffine_fp_y Q) hdp hdm

theorem edExtValid_edExtAdd {P Q : EdExtPoint}
    (hP : EdExtValid P) (hQ : EdExtValid Q) :
    EdExtValid (edExtAdd P Q) where
  z_ne_zero := by
    have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hQ.on_curve
    have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hQ.on_curve
    unfold edExtAdd
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_edD2]
    exact edExtAdd_z_ne_zero_ring _ _ _ _ _ _ _ _ _ _ _ _ _
      Fp.two_ne_zero hP.z_ne_zero hQ.z_ne_zero hP.tz_eq_xy hQ.tz_eq_xy
      (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
      (edExtToAffine_fp_x Q) (edExtToAffine_fp_y Q) hdp hdm
  tz_eq_xy := by
    unfold edExtAdd
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub]
    grind
  on_curve := by
    rw [edExtAdd_toAffine hP hQ]
    exact edOnCurve_edAdd hP.on_curve hQ.on_curve

/-! ## 5. Scalar Multiplication Homomorphism & Basepoint Order ($\ell B = \mathcal{O}$) -/

/-- Peano scalar multiplication $[n]P$ on affine twisted Edwards points for arbitrary $n \in \mathbb{N}$. -/
def edNatSmul : Nat → EdPoint → EdPoint
  | 0, _ => edZero
  | n + 1, P => edAdd P (edNatSmul n P)

@[simp] theorem edNatSmul_zero (P : EdPoint) : edNatSmul 0 P = edZero := rfl
@[simp] theorem edNatSmul_succ (n : Nat) (P : EdPoint) :
    edNatSmul (n + 1) P = edAdd P (edNatSmul n P) := rfl

theorem edOnCurve_edNatSmul (n : Nat) {P : EdPoint} (hP : edOnCurve P = true) :
    edOnCurve (edNatSmul n P) = true := by
  induction n with
  | zero => exact edOnCurve_edZero
  | succ k ih => exact edOnCurve_edAdd hP ih

@[simp] theorem edNatSmul_edZero (n : Nat) : edNatSmul n edZero = edZero := by
  induction n with
  | zero => rfl
  | succ k ih => rw [edNatSmul_succ, ih, edAdd_edZero edOnCurve_edZero]

@[simp] theorem edNatSmul_one {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul 1 P = P := by
  rw [edNatSmul_succ, edNatSmul_zero, edAdd_edZero hP]

theorem edNatSmul_add (m n : Nat) {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul (m + n) P = edAdd (edNatSmul m P) (edNatSmul n P) := by
  induction m with
  | zero =>
    rw [Nat.zero_add, edNatSmul_zero, edZero_edAdd (edOnCurve_edNatSmul n hP)]
  | succ k ih =>
    rw [Nat.succ_add, edNatSmul_succ, edNatSmul_succ, ih,
        edAdd_assoc hP (edOnCurve_edNatSmul k hP) (edOnCurve_edNatSmul n hP)]

theorem edNatSmul_two {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul 2 P = edAdd P P := by
  change edNatSmul (1 + 1) P = edAdd P P
  rw [edNatSmul_add 1 1 hP, edNatSmul_one hP]

theorem edNatSmul_mul (m n : Nat) {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul (m * n) P = edNatSmul m (edNatSmul n P) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.add_comm (k * n) n, edNatSmul_add n (k * n) hP,
        edNatSmul_succ, ih]

theorem edExtSmulLoop_spec (fuel n : Nat) (P acc : EdExtPoint)
    (hn : n < 2 ^ fuel) (hP : EdExtValid P) (hacc : EdExtValid acc) :
    EdExtValid (edExtSmulLoop fuel n P acc) ∧
    edExtToAffine (edExtSmulLoop fuel n P acc) =
      edAdd (edExtToAffine acc) (edNatSmul n (edExtToAffine P)) := by
  induction fuel generalizing n P acc with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0
    refine ⟨hacc, ?_⟩
    rw [edExtSmulLoop, edNatSmul_zero, edAdd_edZero hacc.on_curve]
  | succ fuel ih =>
    unfold edExtSmulLoop
    by_cases h0 : n == 0
    · simp only [h0, ↓reduceIte]
      have hn0 : n = 0 := beq_iff_eq.mp h0
      subst hn0
      refine ⟨hacc, ?_⟩
      rw [edNatSmul_zero, edAdd_edZero hacc.on_curve]
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      have hn_div : n / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hn; omega
      have hPP : EdExtValid (edExtAdd P P) := edExtValid_edExtAdd hP hP
      have hacc' : EdExtValid (if n % 2 == 1 then edExtAdd acc P else acc) := by
        split
        · exact edExtValid_edExtAdd hacc hP
        · exact hacc
      obtain ⟨hvalid, heq⟩ := ih (n / 2) (edExtAdd P P)
        (if n % 2 == 1 then edExtAdd acc P else acc) hn_div hPP hacc'
      refine ⟨hvalid, ?_⟩
      rw [heq, edExtAdd_toAffine hP hP, ← edNatSmul_two hP.on_curve,
          ← edNatSmul_mul (n / 2) 2 hP.on_curve]
      by_cases hodd : n % 2 == 1
      · simp only [hodd, ↓reduceIte]
        have hrem : n % 2 = 1 := beq_iff_eq.mp hodd
        rw [edExtAdd_toAffine hacc hP,
            edAdd_assoc hacc.on_curve hP.on_curve (edOnCurve_edNatSmul _ hP.on_curve),
            ← edNatSmul_succ,
            show n / 2 * 2 + 1 = n by omega]
      · simp only [hodd, Bool.false_eq_true, ↓reduceIte]
        have hrem : n % 2 = 0 := by
          have : n % 2 ≠ 1 := by intro h; exact hodd (beq_iff_eq.mpr h)
          omega
        rw [show n / 2 * 2 = n by omega]

theorem edSmul_eq_edNatSmul {n : Nat} {P : EdPoint}
    (hn : n < 2 ^ 256) (hP : edOnCurve P = true) :
    edSmul n P = edNatSmul n P := by
  unfold edSmul
  obtain ⟨_, heq⟩ := edExtSmulLoop_spec 256 n (edExtOfAffine P) edExtZero
    hn (edExtValid_edExtOfAffine hP) edExtValid_edExtZero
  rw [heq, edExtToAffine_edExtZero, edExtToAffine_edExtOfAffine hP,
      edZero_edAdd (edOnCurve_edNatSmul n hP)]

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

theorem leBytesToNat_cons (b : BitVec 8) (bs : List (BitVec 8)) :
    leBytesToNat (b :: bs) = leBytesToNat bs * 256 + b.toNat := rfl

theorem leBytesToNat_lt (bs : List (BitVec 8)) :
    leBytesToNat bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [leBytesToNat]
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.isLt
    simp only [leBytesToNat_cons, List.length_cons, Nat.pow_succ]
    omega

private theorem leBytesToNat_eq_of_natToLeBytes_eq {bs : List (BitVec 8)} {n : Nat}
    (h : bs = natToLeBytes bs.length n) (hn : n < 256 ^ bs.length) :
    leBytesToNat bs = n := by
  induction bs generalizing n with
  | nil =>
    simp [leBytesToNat] at hn ⊢
    omega
  | cons b bs ih =>
    rw [List.length_cons, Nat.pow_succ'] at hn
    have h0 : b = BitVec.ofNat 8 (n % 256) := by
      have := congrArg (fun l => l[0]?) h
      simpa [natToLeBytes] using this
    have htail : bs = natToLeBytes bs.length (n / 256) := by
      apply List.ext_getElem (by simp [natToLeBytes])
      intro i hi1 _
      have hget := congrArg (fun l => l[i + 1]?) h
      simp only [List.getElem?_cons_succ, List.getElem?_eq_getElem hi1, natToLeBytes,
        List.length_cons, List.getElem?_map, List.getElem?_range (Nat.succ_lt_succ hi1),
        Option.map_some, Option.some.injEq] at hget
      simp only [natToLeBytes, List.getElem_map, List.getElem_range]
      rw [hget, Nat.pow_succ', ← Nat.div_div_eq_div_mul]
    have ih_n := ih htail (by omega)
    simp only [leBytesToNat_cons, ih_n, h0, BitVec.toNat_ofNat]
    omega

theorem leBytesToNat_natToLeBytes_of_lt {len n : Nat} (hn : n < 256 ^ len) :
    leBytesToNat (natToLeBytes len n) = n := by
  have hlen : (natToLeBytes len n).length = len := natToLeBytes_length len n
  exact leBytesToNat_eq_of_natToLeBytes_eq (by rw [hlen]) (by rwa [hlen])

theorem clampScalarBytes_length_le (bs : List (BitVec 8)) :
    (clampScalarBytes bs).length ≤ 32 := by
  unfold clampScalarBytes
  simp only [List.length_append, List.length_singleton, List.length_take, List.length_drop]
  omega

theorem clampScalar_lt_two_pow_256 (bs : List (BitVec 8)) :
    clampScalar bs < 2 ^ 256 := by
  unfold clampScalar
  have hlen : (clampScalarBytes (bs.take 32)).length ≤ 32 :=
    clampScalarBytes_length_le (bs.take 32)
  have hlt := leBytesToNat_lt (clampScalarBytes (bs.take 32))
  have hpow : 256 ^ (clampScalarBytes (bs.take 32)).length ≤ 256 ^ 32 :=
    Nat.pow_le_pow_right (by omega) hlen
  have h256 : 256 ^ 32 = 2 ^ 256 := by decide
  omega

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
theorem edToMontU_lt (P : EdPoint) : edToMontU P < p25519 := fpMul_lt _ _

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

theorem edToMontU_edNeg (P : EdPoint) : edToMontU (edNeg P) = edToMontU P := by
  unfold edToMontU edNeg; rw [fpAdd_mod_right, fpSub_mod_right]

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
/-!
# Subgroup prime orders and group-exponent divisibility

Defines the quadratic-twist subgroup order and proves primality of the Curve25519 subgroup
orders:

1. Prime subgroup order $\ell' = \text{twistOrderL}$ of the quadratic twist $E'(\mathbb{F}_p)$
   and the Hasse–Weil cardinality identity $8\ell + 4\ell' = 2(p_{25519} + 1)$.
2. Pocklington primality proofs `edOrderL_prime : IsPrime edOrderL` and
   `twistOrderL_prime : IsPrime twistOrderL` (witness $a = 2$).
3. Pure-`Nat` Euclidean closure (`nat_pred_gcd`) and cofactor-prime divisibility / GCD lemmas
   for cyclic group order determination and clamped-scalar torsion elimination.
-/

set_option autoImplicit false


namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.OrderPrimality

open X25519Dalek
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field
/-! ## 1. Quadratic-Twist Subgroup Order `twistOrderL` & Basic Arithmetic Bounds -/

/-! ## 2. Certified Pocklington Primality of `edOrderL` ($\ell$) -/

/-! ## 3. Certified Pocklington Primality of `twistOrderL` ($\ell'$) -/

/-! ## 4. Euclidean Kernel Closure & Cofactor-Prime Divisibility / GCD Lemmas -/

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.OrderPrimality
end

section
/-!
# Quadratic Character, Dual Complete Twist Curve $E_{\text{twist}}$, & Montgomery Dichotomy (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1`)

Pure `0-sorry` mathematical proofs for:
1. Quadratic character `FpIsSquare` on $\mathbb{F}_{p_{25519}}$ ($p \equiv 5 \pmod 8$),
   constructive square roots via $a^{(p+3)/8}$ / $\sqrt{-1}$, and Euler Legendre multiplicativity.
2. Dual complete twisted Edwards curve $E_{\text{twist}}(\mathbb{F}_p)$:
   $-x^2 + y^2 = 1 + d^{-1} x^2 y^2$ (`edDInv = fpInv edD`), completeness, abelian group laws,
   and extended homogeneous scalar multiplication `twSmul_eq_twNatSmul`.
3. Montgomery Curve25519 $u$-coordinate dichotomy (`mont_lift_dichotomy`): every nonzero
   $u \in \mathbb{F}_p$ lifts to a non-2-torsion point on either $E(\mathbb{F}_p)$ or
   $E_{\text{twist}}(\mathbb{F}_p)$, partitioned disjointly by `FpIsSquare (Fp.ofNat (montRHS u))`.
-/

set_option autoImplicit false


namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1

open X25519Dalek
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational

/-! ## 1. Quadratic Character (`FpIsSquare`) & Constructive Square Roots in `Fp` -/

theorem fp_ne_of_val_ne {a b : Fp} (h : a.val ≠ b.val) : a ≠ b :=
  fun hab => h (congrArg Fp.val hab)

/-- Quadratic residue predicate on `Fp` ($\mathbb{F}_{p_{25519}}$). -/
def FpIsSquare (a : Fp) : Prop :=
  ∃ r : Fp, r * r = a

theorem fp_isSquare_zero : FpIsSquare 0 := ⟨0, by grind⟩

theorem fp_not_isSquare_inv {a : Fp} (ha : ¬ FpIsSquare a) : ¬ FpIsSquare a⁻¹ := by
  intro hinv
  have ha0 : a ≠ 0 := by intro h0; subst h0; exact ha fp_isSquare_zero
  rcases hinv with ⟨r, hr⟩
  apply ha
  refine ⟨r⁻¹, ?_⟩
  grind

/-! ## 2. Dual Twisted Edwards Constant `edDInv = fpInv edD` & Curve $E_{\text{twist}}$ -/

/-- Inverse twisted Edwards curve constant $d^{-1} = -121666 / 121665 \bmod p_{25519}$ defining the
    dual complete twisted Edwards model $-x^2 + y^2 = 1 + d^{-1} x^2 y^2$ of $E'(\mathbb{F}_p)$. -/
def edDInv : Nat :=
  29203323570479832313932222820853031755424015489030106335172286495629888845891

theorem fpMul_edD_edDInv : fpMul edD edDInv = 1 := by unfold fpMul edD edDInv p25519; decide

theorem fp_edD_mul_edDInv : Fp.ofNat edD * Fp.ofNat edDInv = 1 := by
  have h := congrArg Fp.ofNat fpMul_edD_edDInv
  simpa using h

theorem fp_ofNat_edDInv_eq_inv : Fp.ofNat edDInv = (Fp.ofNat edD)⁻¹ := by
  have h := fp_edD_mul_edDInv
  have hd0 : Fp.ofNat edD ≠ 0 := by intro h0; exact Fp.edD_nonsquare ⟨0, by grind⟩
  grind

theorem fp_edDInv_nonsquare : ¬ FpIsSquare (Fp.ofNat edDInv) := by
  rw [fp_ofNat_edDInv_eq_inv]
  exact fp_not_isSquare_inv Fp.edD_nonsquare

/-- On-curve predicate for the complete quadratic-twist Edwards curve
    $E_{\text{twist}}(\mathbb{F}_p) : -x^2 + y^2 \equiv 1 + d^{-1} x^2 y^2 \pmod{p_{25519}}$. -/
def twOnCurve (P : EdPoint) : Bool :=
  P.x < p25519 && P.y < p25519 &&
  fpAdd (fpNeg (fpSq P.x)) (fpSq P.y) ==
    fpAdd 1 (fpMul edDInv (fpMul (fpSq P.x) (fpSq P.y)))

/-- Complete affine addition on $E_{\text{twist}}(\mathbb{F}_p)$. -/
def twAdd (P Q : EdPoint) : EdPoint :=
  let x1y2 := fpMul P.x Q.y
  let y1x2 := fpMul P.y Q.x
  let y1y2 := fpMul P.y Q.y
  let x1x2 := fpMul P.x Q.x
  let dxxyy := fpMul edDInv (fpMul x1x2 y1y2)
  let x3 := fpMul (fpAdd x1y2 y1x2) (fpInv (fpAdd 1 dxxyy))
  let y3 := fpMul (fpAdd y1y2 x1x2) (fpInv (fpSub 1 dxxyy))
  ⟨x3, y3⟩

abbrev twZero : EdPoint := edZero
abbrev twNeg (P : EdPoint) : EdPoint := edNeg P

/-- Unary Peano scalar multiplication on $E_{\text{twist}}(\mathbb{F}_p)$. -/
def twNatSmul : Nat → EdPoint → EdPoint
  | 0, _ => twZero
  | n + 1, P => twAdd P (twNatSmul n P)

/-! ## 3. Completeness, Abelian Group Laws, & `twSmul_eq_twNatSmul` on $E_{\text{twist}}$ -/

theorem twOnCurve_iff (P : EdPoint) :
    twOnCurve P = true ↔
      P.x < p25519 ∧ P.y < p25519 ∧
      fpAdd (fpNeg (fpSq P.x)) (fpSq P.y) =
        fpAdd 1 (fpMul edDInv (fpMul (fpSq P.x) (fpSq P.y))) := by
  unfold twOnCurve
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc]

theorem twOnCurve_x_lt {P : EdPoint} (hP : twOnCurve P = true) : P.x < p25519 :=
  ((twOnCurve_iff P).mp hP).1

theorem twOnCurve_y_lt {P : EdPoint} (hP : twOnCurve P = true) : P.y < p25519 :=
  ((twOnCurve_iff P).mp hP).2.1

theorem twOnCurve_fp_eq {P : EdPoint} (hP : twOnCurve P = true) :
    -(Fp.ofNat P.x * Fp.ofNat P.x) + Fp.ofNat P.y * Fp.ofNat P.y =
      1 + Fp.ofNat edDInv * ((Fp.ofNat P.x * Fp.ofNat P.x) * (Fp.ofNat P.y * Fp.ofNat P.y)) := by
  have h := congrArg Fp.ofNat ((twOnCurve_iff P).mp hP).2.2
  simpa using h

theorem twOnCurve_of_fp_eq {P : EdPoint} (hx : P.x < p25519) (hy : P.y < p25519)
    (h : -(Fp.ofNat P.x * Fp.ofNat P.x) + Fp.ofNat P.y * Fp.ofNat P.y =
      1 + Fp.ofNat edDInv * ((Fp.ofNat P.x * Fp.ofNat P.x) * (Fp.ofNat P.y * Fp.ofNat P.y))) :
    twOnCurve P = true := by
  rw [twOnCurve_iff]
  refine ⟨hx, hy, Fp.eq_of_ofNat_eq (fpAdd_lt _ _) (fpAdd_lt _ _) ?_⟩
  simpa using h

@[simp] theorem twOnCurve_twZero : twOnCurve twZero = true := by
  unfold twOnCurve twZero edZero fpAdd fpNeg fpSq fpMul edDInv p25519; decide

theorem twOnCurve_twNeg {P : EdPoint} (hP : twOnCurve P = true) :
    twOnCurve (twNeg P) = true := by
  have hfp := twOnCurve_fp_eq hP
  apply twOnCurve_of_fp_eq (fpNeg_lt P.x) (Nat.mod_lt P.y p25519_pos)
  simp only [twNeg, edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod]
  grind

private theorem tw_completeness_ring_id (d x1 y1 x2 y2 j : Fp)
    (h1 : -(x1 * x1) + y1 * y1 = 1 + d * ((x1 * x1) * (y1 * y1)))
    (h2 : -(x2 * x2) + y2 * y2 = 1 + d * ((x2 * x2) * (y2 * y2)))
    (hd : 1 + d * ((x1 * x2) * (y1 * y2)) = 0)
    (hj : j * j = -1) :
    d * ((x1 * y1 * (x2 + j * y2)) * (x1 * y1 * (x2 + j * y2))) =
      (x1 - j * y1) * (x1 - j * y1) := by
  grind

private theorem tw_sq_div {d w v : Fp}
    (h : d * (w * w) = v * v) (hw : w ≠ 0) :
    (v * w⁻¹) * (v * w⁻¹) = d := by
  grind

theorem twAdd_fp_denom_add_ne_zero {P Q : EdPoint}
    (hP : twOnCurve P = true) (hQ : twOnCurve Q = true) :
    (1 : Fp) + Fp.ofNat edDInv * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)) ≠ 0 := by
  intro hd
  let d := Fp.ofNat edDInv
  let x1 := Fp.ofNat P.x
  let y1 := Fp.ofNat P.y
  let x2 := Fp.ofNat Q.x
  let y2 := Fp.ofNat Q.y
  let i := Fp.ofNat sqrtM1
  have h1 : -(x1 * x1) + y1 * y1 = 1 + d * ((x1 * x1) * (y1 * y1)) := twOnCurve_fp_eq hP
  have h2 : -(x2 * x2) + y2 * y2 = 1 + d * ((x2 * x2) * (y2 * y2)) := twOnCurve_fp_eq hQ
  have hi : i * i = -1 := Fp.sqrtM1_sq
  have hni : (-i) * (-i) = -1 := by grind
  have h_pos := tw_completeness_ring_id d x1 y1 x2 y2 i h1 h2 hd hi
  have h_neg := tw_completeness_ring_id d x1 y1 x2 y2 (-i) h1 h2 hd hni
  by_cases h_diff : x1 - i * y1 = 0
  · by_cases h_sum : x1 - (-i) * y1 = 0
    · have h2ne : (2 : Fp) ≠ 0 := Fp.two_ne_zero
      have h10 : (1 : Fp) = 0 := by grind
      exact absurd h10.symm (fp_ne_of_val_ne (by change 0 ≠ 1 % p25519; unfold p25519; decide))
    · have hw_ne : x1 * y1 * (x2 + (-i) * y2) ≠ 0 := by grind
      exact fp_edDInv_nonsquare ⟨_, tw_sq_div h_neg hw_ne⟩
  · have hw_ne : x1 * y1 * (x2 + i * y2) ≠ 0 := by grind
    exact fp_edDInv_nonsquare ⟨_, tw_sq_div h_pos hw_ne⟩

theorem twAdd_fp_denom_sub_ne_zero {P Q : EdPoint}
    (hP : twOnCurve P = true) (hQ : twOnCurve Q = true) :
    (1 : Fp) - Fp.ofNat edDInv * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)) ≠ 0 := by
  have hneg := twAdd_fp_denom_add_ne_zero (twOnCurve_twNeg hP) hQ
  intro h0
  apply hneg
  simp only [twNeg, edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod] at hneg ⊢
  grind

theorem twAdd_x_lt (P Q : EdPoint) : (twAdd P Q).x < p25519 := fpMul_lt _ _
theorem twAdd_y_lt (P Q : EdPoint) : (twAdd P Q).y < p25519 := fpMul_lt _ _

theorem twAdd_fp_x (P Q : EdPoint) :
    Fp.ofNat (twAdd P Q).x =
      (Fp.ofNat P.x * Fp.ofNat Q.y + Fp.ofNat P.y * Fp.ofNat Q.x) *
        (1 + Fp.ofNat edDInv * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)))⁻¹ := by
  unfold twAdd; simp

theorem twAdd_fp_y (P Q : EdPoint) :
    Fp.ofNat (twAdd P Q).y =
      (Fp.ofNat P.y * Fp.ofNat Q.y + Fp.ofNat P.x * Fp.ofNat Q.x) *
        (1 - Fp.ofNat edDInv * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)))⁻¹ := by
  unfold twAdd; simp

theorem twAdd_comm (P Q : EdPoint) : twAdd P Q = twAdd Q P := by
  ext
  · apply Fp.eq_of_ofNat_eq (twAdd_x_lt _ _) (twAdd_x_lt _ _)
    rw [twAdd_fp_x, twAdd_fp_x]; grind
  · apply Fp.eq_of_ofNat_eq (twAdd_y_lt _ _) (twAdd_y_lt _ _)
    rw [twAdd_fp_y, twAdd_fp_y]; grind

@[simp] theorem twAdd_twZero {P : EdPoint} (hP : twOnCurve P = true) :
    twAdd P twZero = P := by
  ext
  · apply Fp.eq_of_ofNat_eq (twAdd_x_lt _ _) (twOnCurve_x_lt hP)
    rw [twAdd_fp_x]; simp only [edZero, Fp.ofNat_zero, Fp.ofNat_one]; grind
  · apply Fp.eq_of_ofNat_eq (twAdd_y_lt _ _) (twOnCurve_y_lt hP)
    rw [twAdd_fp_y]; simp only [edZero, Fp.ofNat_zero, Fp.ofNat_one]; grind

@[simp] theorem twZero_twAdd {P : EdPoint} (hP : twOnCurve P = true) :
    twAdd twZero P = P := by
  rw [twAdd_comm, twAdd_twZero hP]

@[simp] theorem twAdd_twNeg_self {P : EdPoint} (hP : twOnCurve P = true) :
    twAdd P (twNeg P) = twZero := by
  have hfp := twOnCurve_fp_eq hP
  have hdm := twAdd_fp_denom_sub_ne_zero hP (twOnCurve_twNeg hP)
  ext
  · apply Fp.eq_of_ofNat_eq (twAdd_x_lt _ _) (edOnCurve_x_lt edOnCurve_edZero)
    rw [twAdd_fp_x]; simp only [twNeg, edNeg, edZero, Fp.ofNat_fpNeg, Fp.ofNat_mod, Fp.ofNat_zero]
    grind
  · apply Fp.eq_of_ofNat_eq (twAdd_y_lt _ _) (edOnCurve_y_lt edOnCurve_edZero)
    rw [twAdd_fp_y]
    simp only [twNeg, edNeg, edZero, Fp.ofNat_fpNeg, Fp.ofNat_mod, Fp.ofNat_one] at hdm ⊢
    grind

@[simp] theorem twNatSmul_zero (P : EdPoint) : twNatSmul 0 P = twZero := rfl
@[simp] theorem twNatSmul_succ (n : Nat) (P : EdPoint) :
    twNatSmul (n + 1) P = twAdd P (twNatSmul n P) := rfl

@[simp] theorem twNatSmul_twZero (n : Nat) : twNatSmul n twZero = twZero := by
  induction n with
  | zero => rfl
  | succ n ih => rw [twNatSmul_succ, ih, twAdd_twZero twOnCurve_twZero]

/-! ## 4. Montgomery $u$-Coordinate Dichotomy ($E(\mathbb{F}_p)$ vs $E_{\text{twist}}(\mathbb{F}_p)$) -/

/-- Birational Kummer map $u = (y + 1) \cdot (y - 1)^{-1} \bmod p_{25519}$ from $E_{\text{twist}}(\mathbb{F}_p)$
    (maps both $(0, 1)$ and $(0, p - 1)$ to $0$). -/
def twToMontU (P : EdPoint) : Nat :=
  fpMul (fpAdd P.y 1) (fpInv (fpSub P.y 1))

theorem edOnCurve_x_eq_zero_iff {P : EdPoint} (hP : edOnCurve P = true) :
    P.x = 0 ↔ (P = edZero ∨ P = ⟨0, p25519 - 1⟩) := by
  constructor
  · intro hx0
    have hfp := edOnCurve_fp_eq hP
    have hx_fp : Fp.ofNat P.x = 0 := by rw [hx0, Fp.ofNat_zero]
    have hy_sq : Fp.ofNat P.y * Fp.ofNat P.y = 1 := by grind
    have hy_or : Fp.ofNat P.y = 1 ∨ Fp.ofNat P.y = -1 := by grind
    have hy_lt := edOnCurve_y_lt hP
    rcases hy_or with hy1 | hyn1
    · left; ext
      · exact hx0
      · exact Fp.eq_of_ofNat_eq hy_lt (by unfold p25519; decide) hy1
    · right; ext
      · exact hx0
      · apply Fp.eq_of_ofNat_eq hy_lt (by unfold p25519; decide)
        have hm1 : (-1 : Fp) = Fp.ofNat (p25519 - 1) := by ext; unfold Fp.ofNat p25519; decide
        exact hyn1.trans hm1
  · rintro (rfl | rfl) <;> rfl

theorem edToMontU_eq_zero_iff {P : EdPoint} (hP : edOnCurve P = true) :
    edToMontU P = 0 ↔ P.x = 0 := by
  rw [edOnCurve_x_eq_zero_iff hP]
  constructor
  · intro hu0
    have hfp : (1 + Fp.ofNat P.y) * (1 - Fp.ofNat P.y)⁻¹ = 0 := by
      have := congrArg Fp.ofNat hu0
      simpa [edToMontU] using this
    have hy_lt := edOnCurve_y_lt hP
    by_cases h1 : (1 : Fp) - Fp.ofNat P.y = 0
    · left
      have hy1 : Fp.ofNat P.y = 1 := by grind
      have hy_eq : P.y = 1 := Fp.eq_of_ofNat_eq hy_lt (by unfold p25519; decide) hy1
      have hP_zero : P.x = 0 := by
        have hc := edOnCurve_fp_eq hP
        have hsq : Fp.ofNat P.x * Fp.ofNat P.x = 0 := by
          have hd_ne : (1 : Fp) + Fp.ofNat edD ≠ 0 := by
            intro hd0
            exact Fp.edD_nonsquare ⟨Fp.ofNat sqrtM1, by have := Fp.sqrtM1_sq; grind⟩
          grind
        have hx0 : Fp.ofNat P.x = 0 := by grind
        exact Fp.eq_of_ofNat_eq (edOnCurve_x_lt hP) p25519_pos hx0
      ext; exact hP_zero; exact hy_eq
    · right
      have hy_m1 : Fp.ofNat P.y = -1 := by grind
      have hm1 : (-1 : Fp) = Fp.ofNat (p25519 - 1) := by ext; unfold Fp.ofNat p25519; decide
      have hy_eq : P.y = p25519 - 1 :=
        Fp.eq_of_ofNat_eq hy_lt (by unfold p25519; decide) (hy_m1.trans hm1)
      have hP_zero : P.x = 0 := by
        have hc := edOnCurve_fp_eq hP
        have hsq : Fp.ofNat P.x * Fp.ofNat P.x = 0 := by
          have hd_ne : (1 : Fp) + Fp.ofNat edD ≠ 0 := by
            intro hd0
            exact Fp.edD_nonsquare ⟨Fp.ofNat sqrtM1, by have := Fp.sqrtM1_sq; grind⟩
          grind
        have hx0 : Fp.ofNat P.x = 0 := by grind
        exact Fp.eq_of_ofNat_eq (edOnCurve_x_lt hP) p25519_pos hx0
      ext; exact hP_zero; exact hy_eq
  · rintro (rfl | rfl)
    · unfold edToMontU edZero; rw [fpSub_self, fpInv_zero, fpMul_zero]
    · have h0 : fpAdd 1 (p25519 - 1) = 0 := by unfold fpAdd p25519; decide
      unfold edToMontU; dsimp only; rw [h0, zero_fpMul]


end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1
end

section
/-!
# Cyclic Generators, Group Exponents, & Torsion on $E(\mathbb{F}_p)$ and $E_{\text{twist}}(\mathbb{F}_p)$ (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist`)

Pure `0-sorry` mathematical proofs for:
1. Uniqueness of Montgomery $u$-coordinate + $x$-parity lifts on $E(\mathbb{F}_p)$ and $E_{\text{twist}}(\mathbb{F}_p)$.
2. Explicit cyclic generators `genE` (exact order $8 \ell$) and `genTwist` (exact order $4 \ell_{\text{twist}}$).
3. Finite pigeonhole surjectivity (`inj_surj_fin`) and universal group-exponent theorems
   `edNatSmul_eight_mul_edOrderL` (`[8 \cdot \ell] P = \mathcal{O}$ on $E$) and
   `twNatSmul_four_mul_twistOrderL` (`[4 \cdot \ell_{\text{twist}}] P' = \mathcal{O}$ on $E_{\text{twist}}$).
4. Complete $u$-coordinate classification of $E(\mathbb{F}_p)[8]$ (`0, 1, lowOrderU8a, lowOrderU8b`) and
   $E_{\text{twist}}(\mathbb{F}_p)[4]$ (`0, p25519 - 1`).
-/

set_option autoImplicit false


namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist

open X25519Dalek
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.OrderPrimality
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1

/-! ## 1. Uniqueness of Montgomery Lifts (`u` + `x % 2`) -/

@[simp] theorem twToMontU_twNeg (P : EdPoint) : twToMontU (twNeg P) = twToMontU P := by
  unfold twToMontU twNeg edNeg
  rw [fpAdd_mod_left, fpSub_mod_left]

theorem edToMontU_denom_ne_zero {P : EdPoint} (hP : edOnCurve P = true) (hx : P.x ≠ 0) :
    (1 : Fp) - Fp.ofNat P.y ≠ 0 := by
  intro h0
  have hsub0 : fpSub 1 P.y = 0 := by
    apply Fp.eq_of_ofNat_eq (fpSub_lt _ _) p25519_pos
    simpa using h0
  have hu0 : edToMontU P = 0 := by
    unfold edToMontU
    rw [hsub0, fpInv_zero, fpMul_zero]
  exact hx ((edToMontU_eq_zero_iff hP).mp hu0)

/-! ## 2. Cyclic Generators `genE` and `genTwist` and Exact Orders -/

@[simp] theorem twNeg_twAdd_self {P : EdPoint} (hP : twOnCurve P = true) :
    twAdd (twNeg P) P = twZero := by
  rw [twAdd_comm, twAdd_twNeg_self hP]

/-! ## 3. Pure-`Init` Finite Pigeonhole Surjectivity & Universal Group Exponents -/

/-! ## 4. Complete Classification of $E(\mathbb{F}_p)[8]$ and $E_{\text{twist}}(\mathbb{F}_p)[4]$ -/

theorem edNatSmul_two_eq_zero_iff {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul 2 P = edZero ↔ P.x = 0 := by
  rw [edNatSmul_two hP]
  constructor
  · intro h2P
    have hP_eq_neg : P = edNeg P := by
      have h := congrArg (edAdd (edNeg P)) h2P
      rw [← edAdd_assoc (edOnCurve_edNeg hP) hP hP, edNeg_edAdd_self hP,
          edZero_edAdd hP, edAdd_edZero (edOnCurve_edNeg hP)] at h
      exact h
    have hx_neg : P.x = fpNeg P.x := congrArg EdPoint.x hP_eq_neg
    have hxf : Fp.ofNat P.x = -Fp.ofNat P.x := by
      have := congrArg Fp.ofNat hx_neg; simpa using this
    have hx0 : Fp.ofNat P.x = 0 := by have := Fp.two_ne_zero; grind
    exact Fp.eq_of_ofNat_eq (edOnCurve_x_lt hP) p25519_pos hx0
  · intro hx0
    have hneg_eq : edNeg P = P := by
      ext
      · dsimp only [edNeg]; rw [hx0, fpNeg_zero]
      · dsimp only [edNeg]; exact Nat.mod_eq_of_lt (edOnCurve_y_lt hP)
    have h := edAdd_edNeg_self hP
    rw [hneg_eq] at h
    exact h


end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist
end

section
/-!
# Projective Kummer-Line Ladder Soundness on $E(\mathbb{F}_p)$ and $E_{\text{twist}}(\mathbb{F}_p)$ (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Kummer`)

Pure `0-sorry` mathematical proofs for `montDiffAddAndDouble` and `montLadderLoop`:
1. Degenerate $u_1 = 0$ ladder (`montLadderLoop_zero`): every step preserves $U = 0 \lor W = 0$,
   so `fpMul res.U (fpInv res.W) = 0`.
2. Zero-case-split projective Kummer representation `kummerE P Q` on $E(\mathbb{F}_p)$:
   $(U : W) = (\lambda (1 + y) : \lambda (1 - y))$ for $\lambda \in \mathbb{F}_p^\times$,
   preserved unconditionally across `montDiffAddAndDouble` and `montLadderLoop`.
3. Dual zero-case-split projective Kummer representation `kummerTwist P' Q` on $E_{\text{twist}}(\mathbb{F}_p)$:
   $(U : W) = (\lambda (y + 1) : \lambda (y - 1))$ for $\lambda \in \mathbb{F}_p^\times$,
   preserved unconditionally across `montDiffAddAndDouble` and `montLadderLoop`.
-/

set_option autoImplicit false


namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Kummer

open X25519Dalek
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist

/-! ## 1. Degenerate $u_1 = 0$ Montgomery Ladder -/

theorem montDiffAddAndDouble_zero {p0 p1 : MontProjPoint}
    (hp0 : p0.U = 0 ∨ p0.W = 0) :
    (montDiffAddAndDouble 0 p0 p1).1.W = 0 ∧
    (montDiffAddAndDouble 0 p0 p1).2.W = 0 := by
  dsimp only [montDiffAddAndDouble]
  refine ⟨?_, zero_fpMul _⟩
  rcases hp0 with hU | hW
  · rw [hU, zero_fpAdd, zero_fpSub, fpSq_mod, fpSq_fpNeg, fpSub_self, zero_fpMul]
  · rw [hW, fpAdd_zero, fpSub_zero, fpSub_self, zero_fpMul]

theorem montLadderLoop_zero_aux (fuel k : Nat) :
    ∀ (x0 x1 : MontProjPoint),
      (x0.U = 0 ∨ x0.W = 0) →
      (x1.U = 0 ∨ x1.W = 0) →
      (montLadderLoop fuel k 0 x0 x1).U = 0 ∨
      (montLadderLoop fuel k 0 x0 x1).W = 0 := by
  induction fuel with
  | zero =>
    intro x0 _ hx0 _
    exact hx0
  | succ f ih =>
    intro x0 x1 hx0 hx1
    unfold montLadderLoop
    by_cases hb : ((k / 2 ^ f) % 2 == 1) = true
    · simp only [hb, ↓reduceIte]
      obtain ⟨hW0, hW1⟩ := montDiffAddAndDouble_zero (p1 := x0) hx1
      exact ih _ _ (Or.inr hW1) (Or.inr hW0)
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hW0, hW1⟩ := montDiffAddAndDouble_zero (p1 := x1) hx0
      exact ih _ _ (Or.inr hW0) (Or.inr hW1)

theorem montLadderLoop_zero (fuel k : Nat) :
    let res := montLadderLoop fuel k 0 ⟨1, 0⟩ ⟨0, 1⟩
    fpMul res.U (fpInv res.W) = 0 := by
  rcases montLadderLoop_zero_aux fuel k ⟨1, 0⟩ ⟨0, 1⟩ (Or.inr rfl) (Or.inl rfl) with hU | hW
  · dsimp only; rw [hU, zero_fpMul]
  · dsimp only; rw [hW, fpInv_zero, fpMul_zero]

/-! ## 2. Universal Polynomial Ring & Field Helpers -/

private theorem fp_ofNat_a24 : Fp.ofNat a24 = (121665 : Fp) := by
  ext; unfold Fp.ofNat a24 p25519; decide

private theorem proj_ratio_cancel {lam a b : Fp} (hlam : lam ≠ 0) :
    (lam * a) * (lam * b)⁻¹ = a * b⁻¹ := by
  by_cases hb : b = 0
  · subst hb
    have h0 : (0 : Fp)⁻¹ = 0 := by rw [← Fp.ofNat_zero, ← Fp.ofNat_fpInv, fpInv_zero]
    have hl0 : lam * 0 = 0 := by grind
    rw [hl0, h0]; grind
  · grind

private theorem mul_eq_of_eq_mul_inv {a b c : Fp} (hc : c ≠ 0) (h : a = b * c⁻¹) :
    a * c = b := by
  grind

private theorem inv_ne_zero_of_ne_zero {a : Fp} (ha : a ≠ 0) :
    a⁻¹ ≠ 0 ∧ a * a⁻¹ = 1 := by
  grind

private theorem prod5_ne_zero {a b c d e : Fp}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    a * b * c * d * e ≠ 0 := by
  grind

private theorem prod4_ne_zero {a b c d : Fp}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    a * b * c * d ≠ 0 := by
  grind

private theorem prod3_ne_zero {a b c : Fp}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a * b * c ≠ 0 := by
  grind

private theorem sq_ne_zero {a : Fp} (ha : a ≠ 0) :
    a * a ≠ 0 := by
  grind

private theorem one_add_edD_mul_sq_ne_zero (t : Fp) :
    (1 : Fp) + Fp.ofNat edD * (t * t) ≠ 0 := by
  intro h0
  exact Fp.edD_nonsquare ⟨Fp.ofNat sqrtM1 * t⁻¹, by have := Fp.sqrtM1_sq; grind⟩

private theorem x_eq_zero_of_y_neg_one {c d x y : Fp}
    (hcd : c * (1 + d) = 1)
    (hc : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hy : y + 1 = 0) : x = 0 := by
  grind

theorem edOnCurve_one_add_y_ne_zero {P : EdPoint} (hP : edOnCurve P = true) (hx : P.x ≠ 0) :
    (1 : Fp) + Fp.ofNat P.y ≠ 0 := by
  intro h0
  have hcd : (121666 : Fp) * (1 + Fp.ofNat edD) = 1 := by
    ext; unfold Fp.ofNat edD p25519; decide
  have hy : Fp.ofNat P.y + 1 = 0 := by grind
  have hx0 := x_eq_zero_of_y_neg_one hcd (edOnCurve_fp_eq hP) hy
  exact hx (Fp.eq_of_ofNat_eq (edOnCurve_x_lt hP) p25519_pos hx0)

/-- Universal twisted-Edwards differential-addition sum identity (pure `CommRing`). -/
private theorem universal_diffadd_plus (d x y xq yq : Fp)
    (hc : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hcq : -(xq * xq) + yq * yq = 1 + d * ((xq * xq) * (yq * yq))) :
    (1 + d * (y * y)) * (1 + d * (yq * yq)) *
      ((1 - d * ((xq * x) * (yq * y))) + (yq * y + xq * x)) *
      ((1 + d * ((xq * x) * (yq * y))) + (yq * y - xq * x)) =
    (1 + d) * (1 + d * ((y * yq) * (y * yq))) * ((yq + y) * (yq + y)) := by
  grind

/-- Universal twisted-Edwards differential-addition difference identity (pure `CommRing`). -/
private theorem universal_diffadd_minus (d x y xq yq : Fp)
    (hc : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hcq : -(xq * xq) + yq * yq = 1 + d * ((xq * xq) * (yq * yq))) :
    (1 + d * (y * y)) * (1 + d * (yq * yq)) *
      ((1 - d * ((xq * x) * (yq * y))) - (yq * y + xq * x)) *
      ((1 + d * ((xq * x) * (yq * y))) - (yq * y - xq * x)) =
    (1 + d) * (1 + d * ((y * yq) * (y * yq))) * ((yq - y) * (yq - y)) := by
  grind

private theorem aabb_kummerE (y lam2 PU PW : Fp)
    (hPU : PU = lam2 * (1 + y)) (hPW : PW = lam2 * (1 - y)) :
    ((PU + PW) * (PU + PW)) * ((PU - PW) * (PU - PW)) =
      (lam2 * lam2 * lam2 * lam2) * ((16 : Fp) * (y * y)) ∧
    ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW)) *
      ((PU + PW) * (PU + PW) + (121665 : Fp) *
        ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW))) =
      (lam2 * lam2 * lam2 * lam2) *
        ((16 : Fp) * ((1 - y * y) * ((121666 : Fp) - (121665 : Fp) * (y * y)))) := by
  subst hPU; subst hPW; grind

private theorem dbl_curve_E (d x y y2 dm : Fp)
    (hd : (121666 : Fp) * d = -121665)
    (hc : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hdm : dm = 1 - d * ((x * x) * (y * y)))
    (hy2 : y2 * dm = y * y + x * x) :
    (16 : Fp) * (y * y) = ((8 * 121666 : Fp) * (1 + d * (y * y)) * dm) * (1 + y2) ∧
    (16 : Fp) * ((1 - y * y) * ((121666 : Fp) - (121665 : Fp) * (y * y))) =
      ((8 * 121666 : Fp) * (1 + d * (y * y)) * dm) * (1 - y2) := by
  subst hdm; grind

private theorem dbl_kummerE_U2 (d x y y2 dm lam2 PU PW : Fp)
    (hd : (121666 : Fp) * d = -121665)
    (hc : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hdm : dm = 1 - d * ((x * x) * (y * y)))
    (hy2 : y2 * dm = y * y + x * x)
    (hPU : PU = lam2 * (1 + y)) (hPW : PW = lam2 * (1 - y)) :
    ((PU + PW) * (PU + PW)) * ((PU - PW) * (PU - PW)) =
      ((8 * 121666 : Fp) * (lam2 * lam2 * lam2 * lam2) * (1 + d * (y * y)) * dm) * (1 + y2) := by
  rw [(aabb_kummerE y lam2 PU PW hPU hPW).1, (dbl_curve_E d x y y2 dm hd hc hdm hy2).1]
  grind

private theorem dbl_kummerE_W2 (d x y y2 dm lam2 PU PW : Fp)
    (hd : (121666 : Fp) * d = -121665)
    (hc : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hdm : dm = 1 - d * ((x * x) * (y * y)))
    (hy2 : y2 * dm = y * y + x * x)
    (hPU : PU = lam2 * (1 + y)) (hPW : PW = lam2 * (1 - y)) :
    ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW)) *
      ((PU + PW) * (PU + PW) + (121665 : Fp) *
        ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW))) =
      ((8 * 121666 : Fp) * (lam2 * lam2 * lam2 * lam2) * (1 + d * (y * y)) * dm) * (1 - y2) := by
  rw [(aabb_kummerE y lam2 PU PW hPU hPW).2, (dbl_curve_E d x y y2 dm hd hc hdm hy2).2]
  grind

private theorem dacb_kummerE (y yq lam2 lam3 PU PW QU QW : Fp)
    (hPU : PU = lam2 * (1 + y)) (hPW : PW = lam2 * (1 - y))
    (hQU : QU = lam3 * (1 + yq)) (hQW : QW = lam3 * (1 - yq)) :
    ((QU - QW) * (PU + PW) + (QU + QW) * (PU - PW)) *
      ((QU - QW) * (PU + PW) + (QU + QW) * (PU - PW)) =
      (16 : Fp) * (lam2 * lam2) * (lam3 * lam3) * ((yq + y) * (yq + y)) ∧
    ((QU - QW) * (PU + PW) - (QU + QW) * (PU - PW)) *
      ((QU - QW) * (PU + PW) - (QU + QW) * (PU - PW)) =
      (16 : Fp) * (lam2 * lam2) * (lam3 * lam3) * ((yq - y) * (yq - y)) := by
  grind

private theorem combine_diffadd_E
    (c d l16 f1 f2 fyy inv_yy dm dp splus sminus yr y1 u1f Splus Sminus : Fp)
    (hcd : c * (1 + d) = 1)
    (hinv : fyy * inv_yy = 1)
    (hyr : yr * dm = splus)
    (hy1 : y1 * dp = sminus)
    (hu1 : u1f * (1 - y1) = 1 + y1)
    (h1my1 : 1 - y1 ≠ 0)
    (hp : f1 * f2 * (dm + splus) * (dp + sminus) = (1 + d) * fyy * Splus)
    (hm : f1 * f2 * (dm - splus) * (dp - sminus) = (1 + d) * fyy * Sminus) :
    l16 * Splus = (l16 * c * f1 * f2 * inv_yy * (1 + y1) * dm * dp) * (1 + yr) ∧
    u1f * (l16 * Sminus) = (l16 * c * f1 * f2 * inv_yy * (1 + y1) * dm * dp) * (1 - yr) := by
  grind

private theorem montDiffAddAndDouble_fp (u1 : Nat) (p0 p1 : MontProjPoint) :
    let q := montDiffAddAndDouble u1 p0 p1
    let PU := Fp.ofNat p0.U
    let PW := Fp.ofNat p0.W
    let QU := Fp.ofNat p1.U
    let QW := Fp.ofNat p1.W
    Fp.ofNat q.1.U = ((PU + PW) * (PU + PW)) * ((PU - PW) * (PU - PW)) ∧
    Fp.ofNat q.1.W = ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW)) *
      ((PU + PW) * (PU + PW) + (121665 : Fp) *
        ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW))) ∧
    Fp.ofNat q.2.U =
      ((QU - QW) * (PU + PW) + (QU + QW) * (PU - PW)) *
        ((QU - QW) * (PU + PW) + (QU + QW) * (PU - PW)) ∧
    Fp.ofNat q.2.W = Fp.ofNat u1 *
      (((QU - QW) * (PU + PW) - (QU + QW) * (PU - PW)) *
        ((QU - QW) * (PU + PW) - (QU + QW) * (PU - PW))) := by
  dsimp only [montDiffAddAndDouble]
  simp [fp_ofNat_a24]

private theorem mod_pow_two_succ (k f : Nat) :
    k % 2 ^ (f + 1) = ((k / 2 ^ f) % 2) * 2 ^ f + k % 2 ^ f := by
  have hp : 2 ^ (f + 1) = 2 ^ f * 2 := Nat.pow_succ 2 f
  have hdiv := Nat.div_add_mod k (2 ^ f)
  let q := (k / 2 ^ f) / 2
  let b := (k / 2 ^ f) % 2
  have hq : 2 * q + b = k / 2 ^ f := Nat.div_add_mod (k / 2 ^ f) 2
  have hr_lt : k % 2 ^ f < 2 ^ f := Nat.mod_lt k (Nat.two_pow_pos f)
  have hb_lt : b < 2 := Nat.mod_lt _ (by decide)
  have hrem_lt : b * 2 ^ f + k % 2 ^ f < 2 ^ (f + 1) := by
    rw [hp]
    rcases (by omega : b = 0 ∨ b = 1) with hb | hb
    · rw [hb, Nat.zero_mul, Nat.zero_add]; omega
    · rw [hb, Nat.one_mul]; omega
  have hk_eq : k = 2 ^ (f + 1) * q + (b * 2 ^ f + k % 2 ^ f) := by
    calc k = 2 ^ f * (k / 2 ^ f) + k % 2 ^ f := hdiv.symm
      _ = 2 ^ f * (2 * q + b) + k % 2 ^ f := by rw [← hq]
      _ = 2 ^ (f + 1) * q + (b * 2 ^ f + k % 2 ^ f) := by
        rw [hp, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ f) b, Nat.add_assoc]
  conv => lhs; rw [hk_eq]
  rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hrem_lt]

private theorem ladder_exp_step (m b k f : Nat) (hbit : (k / 2 ^ f) % 2 = b) :
    (2 * m + b) * 2 ^ f + k % 2 ^ f = m * 2 ^ (f + 1) + k % 2 ^ (f + 1) := by
  rw [mod_pow_two_succ k f, hbit, Nat.pow_succ, Nat.add_mul,
      Nat.mul_comm 2 m, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm 2 (2 ^ f)]

private theorem montLadderLoop_zero_fuel (k u1 : Nat) (x0 x1 : MontProjPoint) :
    montLadderLoop 0 k u1 x0 x1 = x0 := rfl

/-! ## 3. Projective Kummer Representation on $E(\mathbb{F}_p)$ (`kummerE`) -/

/-- Projective Kummer-line representation on $E(\mathbb{F}_p)$:
    $(U : W) = (\lambda (1 + y) : \lambda (1 - y))$ for some $\lambda \in \mathbb{F}_p^\times$. -/
def kummerE (P : EdPoint) (Q : MontProjPoint) : Prop :=
  ∃ lam : Fp, lam ≠ 0 ∧
    Fp.ofNat Q.U = lam * (1 + Fp.ofNat P.y) ∧
    Fp.ofNat Q.W = lam * (1 - Fp.ofNat P.y)

theorem kummerE_edZero : kummerE edZero ⟨1, 0⟩ := by
  refine ⟨(2 : Fp)⁻¹, (inv_ne_zero_of_ne_zero Fp.two_ne_zero).1, ?_, ?_⟩
  · have h2 := Fp.two_ne_zero
    dsimp only [edZero]; simp only [Fp.ofNat_one]
    grind
  · dsimp only [edZero]; simp only [Fp.ofNat_zero, Fp.ofNat_one]
    grind

theorem kummerE_init {P1 : EdPoint} (hP1 : edOnCurve P1 = true) (hx : P1.x ≠ 0) :
    kummerE P1 ⟨edToMontU P1, 1⟩ := by
  have h1my := edToMontU_denom_ne_zero hP1 hx
  refine ⟨(1 - Fp.ofNat P1.y)⁻¹, (inv_ne_zero_of_ne_zero h1my).1, ?_, ?_⟩
  · unfold edToMontU; simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpInv,
      Fp.ofNat_fpSub, Fp.ofNat_one]
    grind
  · simp only [Fp.ofNat_one]
    grind

theorem kummerE_toMontU {P : EdPoint} {Q : MontProjPoint} (hk : kummerE P Q) :
    fpMul Q.U (fpInv Q.W) = edToMontU P := by
  obtain ⟨lam, hlam, hU, hW⟩ := hk
  apply Fp.eq_of_ofNat_eq (fpMul_lt _ _) (edToMontU_lt P)
  unfold edToMontU
  simp only [Fp.ofNat_fpMul, Fp.ofNat_fpInv, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_one,
    hU, hW]
  exact proj_ratio_cancel hlam

theorem montDiffAddAndDouble_kummerE
    {u1 : Nat} {P Q Q1 : EdPoint} {p0 p1 : MontProjPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true)
    (hQ1_eq : edAdd Q (edNeg P) = Q1)
    (hQ1x : Q1.x ≠ 0) (hu1 : edToMontU Q1 = u1)
    (hk0 : kummerE P p0) (hk1 : kummerE Q p1) :
    kummerE (edAdd P P) (montDiffAddAndDouble u1 p0 p1).1 ∧
    kummerE (edAdd Q P) (montDiffAddAndDouble u1 p0 p1).2 := by
  obtain ⟨lam2, hlam2, hPU, hPW⟩ := hk0
  obtain ⟨lam3, hlam3, hQU, hQW⟩ := hk1
  obtain ⟨hfU2, hfW2, hfU3, hfW3⟩ := montDiffAddAndDouble_fp u1 p0 p1
  have hQ1 : edOnCurve Q1 = true := hQ1_eq ▸ edOnCurve_edAdd hQ (edOnCurve_edNeg hP)
  have hd_rel : (121666 : Fp) * Fp.ofNat edD = -121665 := by
    ext; unfold Fp.ofNat edD p25519; decide
  have hcd : (121666 : Fp) * (1 + Fp.ofNat edD) = 1 := by
    ext; unfold Fp.ofNat edD p25519; decide
  constructor
  · -- Doubling: q0 represents edAdd P P
    have hdm2_ne := edAdd_fp_denom_sub_ne_zero hP hP
    have hy2 := mul_eq_of_eq_mul_inv hdm2_ne (edAdd_fp_y P P)
    have h8_ne : (8 * 121666 : Fp) ≠ 0 :=
      fp_ne_of_val_ne (by change fpMul (8 % p25519) (121666 % p25519) ≠ 0; unfold fpMul p25519; decide)
    have hl4_ne : lam2 * lam2 * lam2 * lam2 ≠ 0 :=
      prod4_ne_zero hlam2 hlam2 hlam2 hlam2
    have hf1_ne := one_add_edD_mul_sq_ne_zero (Fp.ofNat P.y)
    refine ⟨(8 * 121666 : Fp) * (lam2 * lam2 * lam2 * lam2) *
        (1 + Fp.ofNat edD * (Fp.ofNat P.y * Fp.ofNat P.y)) *
        (1 - Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat P.x) * (Fp.ofNat P.y * Fp.ofNat P.y))),
      prod4_ne_zero h8_ne hl4_ne hf1_ne hdm2_ne, ?_, ?_⟩
    · rw [hfU2]
      exact dbl_kummerE_U2 _ _ _ _ _ _ _ _ hd_rel (edOnCurve_fp_eq hP) rfl hy2 hPU hPW
    · rw [hfW2]
      exact dbl_kummerE_W2 _ _ _ _ _ _ _ _ hd_rel (edOnCurve_fp_eq hP) rfl hy2 hPU hPW
  · -- Differential addition: q1 represents edAdd Q P
    have hdm_ne := edAdd_fp_denom_sub_ne_zero hQ hP
    have hyr := mul_eq_of_eq_mul_inv hdm_ne (edAdd_fp_y Q P)
    have hneg_x : Fp.ofNat (edNeg P).x = -Fp.ofNat P.x := by
      dsimp only [edNeg]; simp
    have hneg_y : Fp.ofNat (edNeg P).y = Fp.ofNat P.y := by
      dsimp only [edNeg]; simp
    have hdp_raw := edAdd_fp_denom_sub_ne_zero hQ (edOnCurve_edNeg hP)
    have hy1_raw := hQ1_eq ▸ edAdd_fp_y Q (edNeg P)
    rw [hneg_x, hneg_y] at hdp_raw hy1_raw
    have hdp_eq : (1 : Fp) - Fp.ofNat edD *
        ((Fp.ofNat Q.x * -Fp.ofNat P.x) * (Fp.ofNat Q.y * Fp.ofNat P.y)) =
        1 + Fp.ofNat edD * ((Fp.ofNat Q.x * Fp.ofNat P.x) * (Fp.ofNat Q.y * Fp.ofNat P.y)) := by
      grind
    have hnum_eq : Fp.ofNat Q.y * Fp.ofNat P.y + Fp.ofNat Q.x * -Fp.ofNat P.x =
        Fp.ofNat Q.y * Fp.ofNat P.y - Fp.ofNat Q.x * Fp.ofNat P.x := by grind
    rw [hdp_eq] at hdp_raw hy1_raw
    rw [hnum_eq] at hy1_raw
    have hy1 := mul_eq_of_eq_mul_inv hdp_raw hy1_raw
    have h1my1 := edToMontU_denom_ne_zero hQ1 hQ1x
    have h1py1 := edOnCurve_one_add_y_ne_zero hQ1 hQ1x
    have hu1_fp : Fp.ofNat u1 = (1 + Fp.ofNat Q1.y) * (1 - Fp.ofNat Q1.y)⁻¹ := by
      rw [← hu1]; unfold edToMontU; simp
    have hu1_rel := mul_eq_of_eq_mul_inv h1my1 hu1_fp
    have hf1_ne := one_add_edD_mul_sq_ne_zero (Fp.ofNat P.y)
    have hf2_ne := one_add_edD_mul_sq_ne_zero (Fp.ofNat Q.y)
    have hfyy_ne := one_add_edD_mul_sq_ne_zero (Fp.ofNat P.y * Fp.ofNat Q.y)
    obtain ⟨hinv_ne, hinv_eq⟩ := inv_ne_zero_of_ne_zero hfyy_ne
    obtain ⟨hdacb_p, hdacb_m⟩ := dacb_kummerE _ _ _ _ _ _ _ _ hPU hPW hQU hQW
    have hup := universal_diffadd_plus _ _ _ _ _ (edOnCurve_fp_eq hP) (edOnCurve_fp_eq hQ)
    have hum := universal_diffadd_minus _ _ _ _ _ (edOnCurve_fp_eq hP) (edOnCurve_fp_eq hQ)
    obtain ⟨hU3_eq, hW3_eq⟩ := combine_diffadd_E
      (121666 : Fp) (Fp.ofNat edD) ((16 : Fp) * (lam2 * lam2) * (lam3 * lam3))
      _ _ _ _ _ _ _ _ _ _ _ _ _
      hcd hinv_eq hyr hy1 hu1_rel h1my1 hup hum
    have hl16_ne : (16 : Fp) * (lam2 * lam2) * (lam3 * lam3) ≠ 0 :=
      prod3_ne_zero (fp_ne_of_val_ne (by change 16 % p25519 ≠ 0; unfold p25519; decide))
        (sq_ne_zero hlam2) (sq_ne_zero hlam3)
    have hc_ne : (121666 : Fp) ≠ 0 :=
      fp_ne_of_val_ne (by change 121666 % p25519 ≠ 0; unfold p25519; decide)
    refine ⟨((16 : Fp) * (lam2 * lam2) * (lam3 * lam3)) * (121666 : Fp) *
        (1 + Fp.ofNat edD * (Fp.ofNat P.y * Fp.ofNat P.y)) *
        (1 + Fp.ofNat edD * (Fp.ofNat Q.y * Fp.ofNat Q.y)) *
        (1 + Fp.ofNat edD * ((Fp.ofNat P.y * Fp.ofNat Q.y) * (Fp.ofNat P.y * Fp.ofNat Q.y)))⁻¹ *
        (1 + Fp.ofNat Q1.y) *
        (1 - Fp.ofNat edD * ((Fp.ofNat Q.x * Fp.ofNat P.x) * (Fp.ofNat Q.y * Fp.ofNat P.y))) *
        (1 + Fp.ofNat edD * ((Fp.ofNat Q.x * Fp.ofNat P.x) * (Fp.ofNat Q.y * Fp.ofNat P.y))),
      prod5_ne_zero (prod4_ne_zero hl16_ne hc_ne hf1_ne hf2_ne) hinv_ne h1py1 hdm_ne hdp_raw,
      ?_, ?_⟩
    · rw [hfU3, hdacb_p]; exact hU3_eq
    · rw [hfW3, hdacb_m]; exact hW3_eq

private theorem edNeg_x_ne_zero {P : EdPoint} (hP : edOnCurve P = true) (hx : P.x ≠ 0) :
    (edNeg P).x ≠ 0 := by
  intro h0
  dsimp only [edNeg] at h0
  have h := congrArg fpNeg h0
  rw [fpNeg_fpNeg, fpNeg_zero, Nat.mod_eq_of_lt (edOnCurve_x_lt hP)] at h
  exact hx h

private theorem edAdd_succ_sub_self (m : Nat) {P1 : EdPoint} (hP1 : edOnCurve P1 = true) :
    edAdd (edNatSmul (m + 1) P1) (edNeg (edNatSmul m P1)) = P1 := by
  have hm := edOnCurve_edNatSmul m hP1
  rw [edNatSmul_succ, edAdd_assoc hP1 hm (edOnCurve_edNeg hm),
      edAdd_edNeg_self hm, edAdd_edZero hP1]

private theorem edAdd_sub_succ_self (m : Nat) {P1 : EdPoint} (hP1 : edOnCurve P1 = true) :
    edAdd (edNatSmul m P1) (edNeg (edNatSmul (m + 1) P1)) = edNeg P1 := by
  have hm := edOnCurve_edNatSmul m hP1
  rw [edNatSmul_succ, edNeg_edAdd, edAdd_comm (edNeg P1) (edNeg (edNatSmul m P1)),
      ← edAdd_assoc hm (edOnCurve_edNeg hm) (edOnCurve_edNeg hP1),
      edAdd_edNeg_self hm, edZero_edAdd (edOnCurve_edNeg hP1)]

theorem montLadderLoop_kummerE_aux (fuel k : Nat) {P1 : EdPoint}
    (hP1 : edOnCurve P1 = true) (hP1x : P1.x ≠ 0) :
    ∀ (m : Nat) (x0 x1 : MontProjPoint),
      kummerE (edNatSmul m P1) x0 →
      kummerE (edNatSmul (m + 1) P1) x1 →
      kummerE (edNatSmul (m * 2 ^ fuel + k % 2 ^ fuel) P1)
        (montLadderLoop fuel k (edToMontU P1) x0 x1) := by
  induction fuel with
  | zero =>
    intro m x0 _ hk0 _
    have hm : m * 2 ^ 0 + k % 2 ^ 0 = m := by
      rw [Nat.pow_zero, Nat.mul_one, Nat.mod_one, Nat.add_zero]
    rw [montLadderLoop_zero_fuel, hm]
    exact hk0
  | succ f ih =>
    intro m x0 x1 hk0 hk1
    have hm_on := edOnCurve_edNatSmul m hP1
    have hm1_on := edOnCurve_edNatSmul (m + 1) hP1
    dsimp only [montLadderLoop]
    by_cases hb : ((k / 2 ^ f) % 2 == 1) = true
    · simp only [hb, ↓reduceIte]
      have hbit : (k / 2 ^ f) % 2 = 1 := beq_iff_eq.mp hb
      obtain ⟨hq0, hq1⟩ := montDiffAddAndDouble_kummerE
        hm1_on hm_on (edAdd_sub_succ_self m hP1)
        (edNeg_x_ne_zero hP1 hP1x) (edToMontU_edNeg P1) hk1 hk0
      have h2m1 : edAdd (edNatSmul m P1) (edNatSmul (m + 1) P1) =
          edNatSmul (2 * m + 1) P1 := by
        rw [← edNatSmul_add m (m + 1) hP1]
        exact congrArg (edNatSmul · P1) (by omega)
      have h2m2 : edAdd (edNatSmul (m + 1) P1) (edNatSmul (m + 1) P1) =
          edNatSmul ((2 * m + 1) + 1) P1 := by
        rw [← edNatSmul_add (m + 1) (m + 1) hP1]
        exact congrArg (edNatSmul · P1) (by omega)
      rw [h2m1] at hq1
      rw [h2m2] at hq0
      have hstep := ih (2 * m + 1) _ _ hq1 hq0
      rwa [ladder_exp_step m 1 k f hbit] at hstep
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      have hbit : (k / 2 ^ f) % 2 = 0 := by
        have hne : (k / 2 ^ f) % 2 ≠ 1 := fun h => hb (beq_iff_eq.mpr h)
        omega
      obtain ⟨hq0, hq1⟩ := montDiffAddAndDouble_kummerE
        hm_on hm1_on (edAdd_succ_sub_self m hP1) hP1x rfl hk0 hk1
      have h2m : edAdd (edNatSmul m P1) (edNatSmul m P1) = edNatSmul (2 * m) P1 := by
        rw [← edNatSmul_add m m hP1]
        exact congrArg (edNatSmul · P1) (by omega)
      have h2m1 : edAdd (edNatSmul (m + 1) P1) (edNatSmul m P1) =
          edNatSmul (2 * m + 1) P1 := by
        rw [← edNatSmul_add (m + 1) m hP1]
        exact congrArg (edNatSmul · P1) (by omega)
      rw [h2m] at hq0
      rw [h2m1] at hq1
      have hstep := ih (2 * m) _ _ hq0 hq1
      have hexp := ladder_exp_step m 0 k f hbit
      rw [Nat.add_zero] at hexp
      rwa [hexp] at hstep

/-- **Montgomery 255-Step Ladder Soundness on $E(\mathbb{F}_p)$**:
    For any $P_1 \in E(\mathbb{F}_p)$ with $P_1.x \ne 0$ and any $k < 2^{255}$,
    running `montLadderLoop 255 k u1 ⟨1, 0⟩ ⟨u1, 1⟩` computes $u([k] P_1)$. -/
theorem montLadderLoop_255_edToMontU {k : Nat} {P1 : EdPoint}
    (hk : k < 2 ^ 255) (hP1 : edOnCurve P1 = true) (hP1x : P1.x ≠ 0) :
    let u1 := edToMontU P1
    let res := montLadderLoop 255 k u1 ⟨1, 0⟩ ⟨u1, 1⟩
    fpMul res.U (fpInv res.W) = edToMontU (edNatSmul k P1) := by
  dsimp only
  have hk0 : kummerE (edNatSmul 0 P1) ⟨1, 0⟩ := kummerE_edZero
  have hk1 : kummerE (edNatSmul (0 + 1) P1) ⟨edToMontU P1, 1⟩ := by
    rw [Nat.zero_add, edNatSmul_one hP1]
    exact kummerE_init hP1 hP1x
  have hloop := montLadderLoop_kummerE_aux 255 k hP1 hP1x 0 _ _ hk0 hk1
  rw [Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hk] at hloop
  exact kummerE_toMontU hloop

/-! ## 4. Projective Kummer Representation on $E_{\text{twist}}(\mathbb{F}_p)$ (`kummerTwist`) -/


end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Kummer
end

section
/-!
# RFC 7748 Montgomery Ladder & X25519 Algebraic Bridges (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder`)

Pure `0-sorry` mathematical bridge theorems for `x25519Ladder`, `x25519`, `x25519Pubkey`,
`x25519Ref`, `x25519PubFromSecretRef`, and `isCanonicalX25519`:
1. 255-step Kummer-line ladder soundness on all of $E(\mathbb{F}_p)$ (`x25519Ladder_edToMontU`,
   `montLadderLoop_255_edToMontU`) and $E_{\text{twist}}(\mathbb{F}_p)$ (`x25519Ladder_twToMontU`,
   `montLadderLoop_255_twToMontU`), including the degenerate $u = 0$ ($x = 0$) 2-torsion fiber.
2. Congruence mod $p_{25519}$ (`x25519_uCoord_congr`), basepoint identity (`edToMontU_edBasepoint`,
   `x25519Pubkey_eq_edBasepoint`), and Diffie–Hellman commutativity (`x25519_comm`, `x25519Ref_comm`).
3. Complete all-zero / low-order output characterization (`x25519_eq_zero_iff_lowOrder`,
   `x25519Ref_eq_zero_iff_lowOrder`), public-key non-low-order (`x25519Pubkey_not_lowOrder`), and
   non-zero Diffie–Hellman agreement on derived public keys (`x25519_pub_ne_zero`).
4. Preservation of `libsignal-core` prime-order canonicality (`isCanonicalX25519_x25519`) and
   prime-order subgroup Kummer-line bijectivity / scalar action for `X25519Model`.
-/

set_option autoImplicit false


namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder

open X25519Dalek
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.OrderPrimality
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Kummer

/-! ## 1. 255-Step Kummer-Line Ladder Soundness (Curve, Twist, & $u = 0$) -/

/-- 255-step Kummer-line ladder soundness on $E(\mathbb{F}_p)$ for $P.x \ne 0$. -/
theorem montLadderLoop_255_edToMontU {k : Nat} {P : EdPoint}
    (hk : k < 2 ^ 255) (hP : edOnCurve P = true) (hPx : P.x ≠ 0) :
    let u1 := edToMontU P
    let res := montLadderLoop 255 k u1 ⟨1, 0⟩ ⟨u1, 1⟩
    fpMul res.U (fpInv res.W) = edToMontU (edNatSmul k P) :=
  LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Kummer.montLadderLoop_255_edToMontU hk hP hPx

theorem x25519Ladder_mod (k u : Nat) :
    x25519Ladder k (u % p25519) = x25519Ladder k u := by
  unfold x25519Ladder
  dsimp only []
  rw [Nat.mod_mod]

theorem x25519Ladder_zero (k : Nat) :
    x25519Ladder k 0 = 0 := by
  unfold x25519Ladder
  dsimp only []
  rw [Nat.zero_mod]
  exact montLadderLoop_zero 255 k

/-- Full 255-step `x25519Ladder` soundness on $E(\mathbb{F}_p)$ for **all** curve points `P`
    (including `edZero` and the 2-torsion point `(0, p - 1)`). -/
theorem x25519Ladder_edToMontU {k : Nat} {P : EdPoint}
    (hk : k < 2 ^ 255) (hP : edOnCurve P = true) :
    x25519Ladder k (edToMontU P) = edToMontU (edNatSmul k P) := by
  by_cases hPx : P.x = 0
  · have hu0 : edToMontU P = 0 := (edToMontU_eq_zero_iff hP).mpr hPx
    rw [hu0, x25519Ladder_zero]
    have h2P : edNatSmul 2 P = edZero := (edNatSmul_two_eq_zero_iff hP).mpr hPx
    have h2kP : edNatSmul 2 (edNatSmul k P) = edZero := by
      rw [← edNatSmul_mul 2 k hP, Nat.mul_comm 2 k, edNatSmul_mul k 2 hP, h2P, edNatSmul_edZero]
    have hk_on : edOnCurve (edNatSmul k P) = true := edOnCurve_edNatSmul k hP
    exact ((edToMontU_eq_zero_iff hk_on).mpr ((edNatSmul_two_eq_zero_iff hk_on).mp h2kP)).symm
  · unfold x25519Ladder
    dsimp only []
    rw [Nat.mod_eq_of_lt (edToMontU_lt P)]
    exact montLadderLoop_255_edToMontU hk hP hPx

/-! ## 2. Clamped ScalarCofactor-8 Decomposition, Congruence, & Commutativity -/

set_option maxRecDepth 8000 in
private theorem all_u8_clamp_masks :
    (List.range 256).all (fun n =>
      let b : BitVec 8 := BitVec.ofNat 8 n
      ((b &&& 0xf8#8).toNat % 8 == 0) &&
      (64 ≤ ((b &&& 0x7f#8) ||| 0x40#8).toNat) &&
      (((b &&& 0x7f#8) ||| 0x40#8).toNat < 128)) = true := by
  decide

private theorem mask_f8_props (b : BitVec 8) :
    (b &&& 0xf8#8).toNat % 8 = 0 ∧ (b &&& 0xf8#8).toNat < 256 := by
  have hb_eq : BitVec.ofNat 8 b.toNat = b :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt b.isLt])
  have hall := List.all_eq_true.mp all_u8_clamp_masks b.toNat (List.mem_range.mpr b.isLt)
  dsimp only at hall
  rw [hb_eq] at hall
  simp only [Bool.and_eq_true, beq_iff_eq] at hall
  exact ⟨hall.1.1, (b &&& 0xf8#8).isLt⟩

private theorem mask_7f_40_props (b : BitVec 8) :
    64 ≤ ((b &&& 0x7f#8) ||| 0x40#8).toNat ∧
    ((b &&& 0x7f#8) ||| 0x40#8).toNat < 128 := by
  have hb_eq : BitVec.ofNat 8 b.toNat = b :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt b.isLt])
  have hall := List.all_eq_true.mp all_u8_clamp_masks b.toNat (List.mem_range.mpr b.isLt)
  dsimp only at hall
  rw [hb_eq] at hall
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  exact ⟨hall.1.2, hall.2⟩

private theorem leBytesToNat_append_singleton (bs : List (BitVec 8)) (b : BitVec 8) :
    leBytesToNat (bs ++ [b]) = leBytesToNat bs + b.toNat * 256 ^ bs.length := by
  induction bs with
  | nil =>
    simp [leBytesToNat]
  | cons c cs ih =>
    rw [List.cons_append, leBytesToNat_cons, ih, leBytesToNat_cons, List.length_cons,
        Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.add_right_comm]

private theorem pow_256_pos (n : Nat) : 1 ≤ 256 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    exact Nat.le_trans ih (Nat.le_mul_of_pos_right _ (by decide))

/-- Every RFC 7748 / RFC 8032 clamped scalar `clampScalar s` decomposes as `8 * m` with
    `0 < m < 2 ^ 252`. -/
theorem clampScalar_eight_mul (s : List (BitVec 8)) :
    ∃ m : Nat, clampScalar s = 8 * m ∧ 0 < m ∧ m < 2 ^ 252 := by
  unfold clampScalar clampScalarBytes
  let bs := s.take 32
  let b0 := (bs.getD 0 0#8) &&& 0xf8#8
  let mid := (bs.drop 1).take 30
  let b31 := ((bs.getD 31 0#8) &&& 0x7f#8) ||| 0x40#8
  change ∃ m : Nat, leBytesToNat ([b0] ++ mid ++ [b31]) = 8 * m ∧ 0 < m ∧ m < 2 ^ 252
  have hcons : [b0] ++ mid ++ [b31] = b0 :: (mid ++ [b31]) := rfl
  rw [hcons, leBytesToNat_cons, leBytesToNat_append_singleton]
  obtain ⟨hb0_mod, hb0_lt⟩ := mask_f8_props (bs.getD 0 0#8)
  obtain ⟨hb31_ge, hb31_lt⟩ := mask_7f_40_props (bs.getD 31 0#8)
  have hmid_len : mid.length ≤ 30 := List.length_take_le 30 _
  have hmid_lt : leBytesToNat mid < 256 ^ mid.length := leBytesToNat_lt mid
  have hpow_ge : 1 ≤ 256 ^ mid.length := pow_256_pos mid.length
  have hpow_le : 256 ^ mid.length ≤ 256 ^ 30 := Nat.pow_le_pow_right (by decide) hmid_len
  let H := leBytesToNat mid + b31.toNat * 256 ^ mid.length
  have hH_pos : 64 ≤ H := by
    have h1 : 64 * 1 ≤ 64 * 256 ^ mid.length := Nat.mul_le_mul_left 64 hpow_ge
    have h2 : 64 * 256 ^ mid.length ≤ b31.toNat * 256 ^ mid.length :=
      Nat.mul_le_mul_right _ hb31_ge
    dsimp only [H]; omega
  have hH_lt : H < 2 ^ 247 := by
    have h1 : b31.toNat * 256 ^ mid.length ≤ 127 * 256 ^ mid.length :=
      Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt hb31_lt)
    have h2 : H < 128 * 256 ^ mid.length := by
      dsimp only [H]
      generalize 256 ^ mid.length = P at hmid_lt h1
      omega
    have h3 : 128 * 256 ^ mid.length ≤ 128 * 256 ^ 30 := Nat.mul_le_mul_left 128 hpow_le
    have h4 : 128 * 256 ^ 30 = 2 ^ 247 := by decide +kernel
    exact Nat.lt_of_lt_of_le h2 (h4 ▸ h3)
  refine ⟨H * 32 + b0.toNat / 8, ?_, ?_, ?_⟩
  · dsimp only [b0] at hb0_mod hb0_lt ⊢
    change H * 256 + ((bs.getD 0 0#8) &&& 0xf8#8).toNat =
      8 * (H * 32 + ((bs.getD 0 0#8) &&& 0xf8#8).toNat / 8)
    generalize ((bs.getD 0 0#8) &&& 0xf8#8).toNat = B0 at hb0_mod hb0_lt ⊢
    omega
  · omega
  · have hH_le : H ≤ 2 ^ 247 - 1 := Nat.le_sub_one_of_lt hH_lt
    have hH32 : H * 32 ≤ (2 ^ 247 - 1) * 32 := Nat.mul_le_mul_right 32 hH_le
    have hb0_div : b0.toNat / 8 ≤ 31 := by dsimp only [b0]; omega
    have hbound : (2 ^ 247 - 1) * 32 + 31 < 2 ^ 252 := by decide +kernel
    exact Nat.lt_of_le_of_lt (Nat.add_le_add hH32 hb0_div) hbound

theorem clampScalar_lt_two_pow_255 (s : List (BitVec 8)) :
    clampScalar s < 2 ^ 255 := by
  obtain ⟨m, hk, _, hm_lt⟩ := clampScalar_eight_mul s
  calc clampScalar s = 8 * m := hk
    _ < 8 * 2 ^ 252 := Nat.mul_lt_mul_of_pos_left hm_lt (by decide)
    _ = 2 ^ 255 := by decide +kernel

private theorem natToLeBytes_length (len n : Nat) :
    (natToLeBytes len n).length = len := by
  unfold natToLeBytes
  rw [List.length_map, List.length_range]

private theorem decodeU255_natToLeBytes_mod_p {v : Nat} (hv : v < p25519) :
    decodeU255 (natToLeBytes 32 v) % p25519 = v := by
  unfold decodeU255
  have htake : (natToLeBytes 32 v).take 32 = natToLeBytes 32 v :=
    List.take_of_length_le (Nat.le_of_eq (natToLeBytes_length 32 v))
  have hv255 : v < 2 ^ 255 := Nat.lt_trans hv (by unfold p25519; decide +kernel)
  have hv256 : v < 256 ^ 32 := Nat.lt_trans hv255 (by decide +kernel)
  rw [htake, leBytesToNat_natToLeBytes_of_lt hv256, Nat.mod_eq_of_lt hv255, Nat.mod_eq_of_lt hv]

theorem x25519Pubkey_eq_edNatSmul (s : List (BitVec 8)) :
    x25519Pubkey s = natToLeBytes 32 (edToMontU (edNatSmul (clampScalar s) edBasepoint)) := by
  unfold x25519Pubkey x25519 x25519Basepoint
  rw [← x25519Ladder_mod,
      decodeU255_natToLeBytes_mod_p (by unfold p25519; decide +kernel : 9 < p25519),
      ← edToMontU_edBasepoint,
      x25519Ladder_edToMontU (clampScalar_lt_two_pow_255 s) edOnCurve_edBasepoint]

/-- X25519 public-key / Ed25519 basepoint bridge: `x25519Pubkey s` equals the 32-byte little-endian
    encoding of `edToMontU (edSmul (clampScalar s) edBasepoint)`. -/
theorem x25519Pubkey_eq_edBasepoint (s : List (BitVec 8)) :
    x25519Pubkey s = natToLeBytes 32 (edToMontU (edSmul (clampScalar s) edBasepoint)) := by
  rw [x25519Pubkey_eq_edNatSmul s,
      ← edSmul_eq_edNatSmul (clampScalar_lt_two_pow_256 s) edOnCurve_edBasepoint]


/-! ## 3. All-Zero / Low-Order Output Characterization & Derived Public-Key Non-Degeneracy -/

/-! ## 4. Canonicality Preservation (`isCanonicalX25519_x25519`) -/

/-! ## 5. Prime-Order Subgroup Kummer-Line Helpers (`X25519Model` / `ConsumerBridges`) -/

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder
end

open X25519Dalek in
theorem solution (s : List (BitVec 8)) :
    x25519Pubkey s = natToLeBytes 32 (edToMontU (edSmul (clampScalar s) edBasepoint)) :=
  LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder.x25519Pubkey_eq_edBasepoint s
