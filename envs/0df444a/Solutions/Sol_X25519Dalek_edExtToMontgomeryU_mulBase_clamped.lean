-- Prove2me | solution 1 for X25519Dalek.edExtToMontgomeryU_mulBase_clamped
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T11:56:39.957334+00:00
-- url     : https://prove2.me/submissions/447164bb-ea7c-42ae-97bb-994307aa6fa9

import Definitions.Def_X25519Dalek_PlacedObj
import Definitions.Def_X25519Dalek_Rfc7748
import Definitions.Def_X25519Dalek_Spec
import Theorems.Thm_X25519Dalek_x25519Pubkey_eq_edToMontU
import Mathlib

section
section
set_option autoImplicit false

namespace ProofLib

/-- Pack 8 little-endian bytes into a 64-bit word. -/
def pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0

end ProofLib

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.ScalarMul1

open ProofLib
open X25519Dalek

/-- Extract `rem` consecutive little-endian `u64` words from `bs`. -/
def readWords64 : List (BitVec 8) → Nat → List (BitVec 64)
  | _, 0 => []
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, rem + 1 =>
    pack64 b0 b1 b2 b3 b4 b5 b6 b7 :: readWords64 rest rem
  | _, _ + 1 => []

/-- Group `rem` 5-word `FieldElement51` chunks into canonical residues modulo `p25519`. -/
def fe51ValsFromWords : List (BitVec 64) → Nat → List Nat
  | _, 0 => []
  | w0 :: w1 :: w2 :: w3 :: w4 :: rest, rem + 1 =>
    (fe51Val w0 w1 w2 w3 w4 % p25519) :: fe51ValsFromWords rest rem
  | _, _ + 1 => []

/-- Group `rem` triples of `FieldElement51` values into `(y_plus_x, y_minus_x, xy2d)` tuples. -/
def nielsFromVals : List Nat → Nat → List (Nat × Nat × Nat)
  | _, 0 => []
  | v0 :: v1 :: v2 :: rest, rem + 1 =>
    (v0, v1, v2) :: nielsFromVals rest rem
  | _, _ + 1 => []

/-- Extract `m` consecutive 120-byte `AffineNielsPoint` tuples modulo `p25519` from `bs`. -/
def nielsFromBytes (bs : List (BitVec 8)) (m : Nat) : List (Nat × Nat × Nat) :=
  nielsFromVals (fe51ValsFromWords (readWords64 bs (15 * m)) (3 * m)) m

/-- Projective check (without `fpInv`) that `(ypx, ymx, xy2d)` are the canonical `AffineNiels`
    coordinates modulo `p25519` of extended point `P` with `P.Z % p25519 ≠ 0`. -/
def checkNielsEntry (e : Nat × Nat × Nat) (P : EdExtPoint) : Bool :=
  let (ypx, ymx, xy2d) := e
  (P.Z % p25519 != 0) &&
  (fpMul ypx P.Z == fpAdd P.Y P.X) &&
  (fpMul ymx P.Z == fpSub P.Y P.X) &&
  (fpMul xy2d P.Z == fpMul edD2 P.T)

/-- Check `rem` consecutive entries of an 8-entry `LookupTable<AffineNielsPoint>` starting from
    accumulator `acc` (`[j] Bi`), advancing by `Bi` at each step. -/
def checkTable8 : List (Nat × Nat × Nat) → EdExtPoint → EdExtPoint → Nat → Bool
  | _, _, _, 0 => true
  | e :: rest, Bi, acc, rem + 1 =>
    let acc' := edExtAdd acc Bi
    checkNielsEntry e acc' && checkTable8 rest Bi acc' rem
  | [], _, _, _ + 1 => false

/-- Check `rem` consecutive 8-entry basepoint tables starting at `Bi = [256^i] B`, advancing
    `Bi ↦ [256] Bi = edDouble4 (edDouble4 Bi)`. -/
def checkBasepointTable32 : List (Nat × Nat × Nat) → EdExtPoint → Nat → Bool
  | _, _, 0 => true
  | entries, Bi, rem + 1 =>
    (entries.take 8).length == 8 &&
    checkTable8 (entries.take 8) Bi edExtZero 8 &&
    checkBasepointTable32 (entries.drop 8) (edDouble4 (edDouble4 Bi)) rem

theorem nielsFromBytes_ed25519BasepointTable_length :
    (nielsFromBytes ed25519BasepointTableBytes 256).length = 256 := by decide +kernel

theorem checkBasepointTable32_ed25519 :
    checkBasepointTable32 (nielsFromBytes ed25519BasepointTableBytes 256)
      (edExtOfAffine edBasepoint) 32 = true := by decide +kernel


end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.ScalarMul1

end
end

section
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

end X25519Dalek

end
end

section
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
end

section
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

/-- A synonym of `Fp` carrying a Mathlib commutative ring structure built from its `Lean.Grind`
    one, so that the two associativity identities below are checked by `linear_combination`. -/
private def FpR : Type := Fp

private instance FpR.instAdd : Add FpR := ⟨@HAdd.hAdd Fp Fp Fp _⟩
private instance FpR.instMul : Mul FpR := ⟨@HMul.hMul Fp Fp Fp _⟩
private instance FpR.instSub : Sub FpR := ⟨@HSub.hSub Fp Fp Fp _⟩
private instance FpR.instNeg : Neg FpR := ⟨@Neg.neg Fp _⟩
private instance FpR.instZero : Zero FpR := ⟨(0 : Fp)⟩
private instance FpR.instOne : One FpR := ⟨(1 : Fp)⟩
private instance FpR.instNatCast : NatCast FpR := ⟨Nat.unaryCast⟩
private instance FpR.instIntCast : IntCast FpR := ⟨Int.castDef⟩

private def Fp.commRing : CommRing FpR where
  add_assoc := @Lean.Grind.Semiring.add_assoc Fp _
  zero_add a := (Lean.Grind.Semiring.add_comm (α := Fp) 0 a).trans (Lean.Grind.Semiring.add_zero (α := Fp) a)
  add_zero := @Lean.Grind.Semiring.add_zero Fp _
  add_comm := @Lean.Grind.Semiring.add_comm Fp _
  neg_add_cancel := @Lean.Grind.Ring.neg_add_cancel Fp _
  sub_eq_add_neg := @Lean.Grind.Ring.sub_eq_add_neg Fp _
  left_distrib := @Lean.Grind.Semiring.left_distrib Fp _
  right_distrib := @Lean.Grind.Semiring.right_distrib Fp _
  zero_mul := @Lean.Grind.Semiring.zero_mul Fp _
  mul_zero := @Lean.Grind.Semiring.mul_zero Fp _
  mul_assoc := @Lean.Grind.Semiring.mul_assoc Fp _
  one_mul := @Lean.Grind.Semiring.one_mul Fp _
  mul_one := @Lean.Grind.Semiring.mul_one Fp _
  mul_comm := @Lean.Grind.CommRing.mul_comm Fp _
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec

private theorem edAdd_assoc_x_ring_gen {F : Type} [CommRing F] (d x1 y1 x2 y2 x3 y3 : F)
    (h1 : d * ((x1 * x1) * (y1 * y1)) = -(x1 * x1) + y1 * y1 - 1)
    (h2 : d * ((x2 * x2) * (y2 * y2)) = -(x2 * x2) + y2 * y2 - 1)
    (h3 : d * ((x3 * x3) * (y3 * y3)) = -(x3 * x3) + y3 * y3 - 1) :
        ((x1 * y2 + y1 * x2) * (1 - d * ((x1 * x2) * (y1 * y2))) * y3 + (y1 * y2 + x1 * x2) * (1 + d * ((x1 * x2) * (y1 * y2))) * x3) * ((1 + d * ((x2 * x3) * (y2 * y3))) * (1 - d * ((x2 * x3) * (y2 * y3))) + d * ((x1 * (x2 * y3 + y2 * x3)) * (y1 * (y2 * y3 + x2 * x3)))) =
            (x1 * (1 + d * ((x2 * x3) * (y2 * y3))) * (y2 * y3 + x2 * x3) + y1 * (1 - d * ((x2 * x3) * (y2 * y3))) * (x2 * y3 + y2 * x3)) * ((1 + d * ((x1 * x2) * (y1 * y2))) * (1 - d * ((x1 * x2) * (y1 * y2))) + d * (((x1 * y2 + y1 * x2) * x3) * ((y1 * y2 + x1 * x2) * y3))) := by
  linear_combination (d * x1 * x3 * x2 * x2 * x2 * y2 * y2 + d * x1 * y3 * x2 * x2 * y2 * y2 * y2 + d * x1 * x2 * x2 * x2 * x3 * x3 * x3 * y2 * y2 + d * x3 * y1 * x2 * x2 * y2 * y2 * y2 + d * y1 * y3 * x2 * x2 * x2 * y2 * y2 + d * y1 * x2 * x2 * x3 * x3 * x3 * y2 * y2 * y2 - d * x1 * x2 * x2 * y2 * y2 * y2 * y3 * y3 * y3 - d * y1 * x2 * x2 * x2 * y2 * y2 * y3 * y3 * y3 + d * x1 * y2 * y3 * x2 * x2 * x2 * x2 * x3 * x3 + d * x2 * y1 * y3 * x3 * x3 * y2 * y2 * y2 * y2 + x1 * x3 * d * d * x2 * x2 * x2 * y2 * y2 * y2 * y2 * y3 * y3 + x1 * y3 * d * d * x2 * x2 * x2 * x2 * x3 * x3 * y2 * y2 * y2 - d * x1 * x2 * x3 * y2 * y2 * y2 * y2 * y3 * y3 - d * x3 * y1 * y2 * x2 * x2 * x2 * x2 * y3 * y3 - x3 * y1 * d * d * x2 * x2 * x2 * x2 * y2 * y2 * y2 * y3 * y3 - y1 * y3 * d * d * x2 * x2 * x2 * x3 * x3 * y2 * y2 * y2 * y2) * h1 + (x1 * y2 * y3 * y3 * y3 + x2 * y1 * y3 * y3 * y3 + x2 * y3 * y1 * y1 * y1 + x3 * y2 * y1 * y1 * y1 + y2 * x1 * x1 * x1 * y3 * y3 * y3 + y2 * x3 * x3 * x3 * y1 * y1 * y1 - x1 * x2 * x3 - x1 * x2 * x3 * x3 * x3 - x1 * y2 * y3 - x2 * x3 * x1 * x1 * x1 - x2 * y1 * y3 - x2 * x1 * x1 * x1 * x3 * x3 * x3 - x2 * y1 * y1 * y1 * y3 * y3 * y3 - x3 * y1 * y2 - y1 * y2 * x3 * x3 * x3 - y2 * y3 * x1 * x1 * x1 + x1 * x2 * x3 * y1 * y1 + x1 * x2 * x3 * y3 * y3 + x1 * x2 * x3 * x3 * x3 * y1 * y1 + x1 * y2 * y3 * y1 * y1 + x2 * x3 * x1 * x1 * x1 * y3 * y3 + x2 * y1 * x1 * x1 * y3 * y3 * y3 + x2 * y3 * x3 * x3 * y1 * y1 * y1 + x3 * y1 * y2 * y3 * y3 - x1 * y2 * y3 * x3 * x3 - x1 * y2 * y1 * y1 * y3 * y3 * y3 - x2 * y1 * y3 * x1 * x1 - x2 * y1 * y3 * x3 * x3 - x3 * y1 * y2 * x1 * x1 - x3 * y2 * y1 * y1 * y1 * y3 * y3 - y1 * y2 * x1 * x1 * x3 * x3 * x3 - y2 * y3 * x1 * x1 * x1 * x3 * x3 + d * x2 * x3 * x3 * y1 * y1 * y1 * y3 * y3 * y3 + d * y2 * x3 * x3 * x3 * y1 * y1 * y1 * y3 * y3 + x1 * y2 * y3 * x3 * x3 * y1 * y1 + x3 * y1 * y2 * x1 * x1 * y3 * y3 - d * x1 * x2 * x3 * x3 * x3 * y3 * y3 - d * x1 * y2 * x3 * x3 * y3 * y3 * y3 - d * x2 * y1 * x3 * x3 * y3 * y3 * y3 - d * x2 * x1 * x1 * x1 * x3 * x3 * x3 * y3 * y3 - d * y1 * y2 * x3 * x3 * x3 * y3 * y3 - d * y2 * x1 * x1 * x1 * x3 * x3 * y3 * y3 * y3 - x1 * x2 * x3 * y1 * y1 * y3 * y3 - x2 * y1 * y3 * x1 * x1 * x3 * x3 + d * x1 * x2 * x3 * x3 * x3 * y1 * y1 * y3 * y3 + d * x1 * y2 * x3 * x3 * y1 * y1 * y3 * y3 * y3 + d * x2 * y1 * y3 * x3 * x3 * y2 * y2 + d * x3 * y1 * y2 * x2 * x2 * y3 * y3 - d * x1 * x2 * x3 * y2 * y2 * y3 * y3 - d * x1 * y2 * y3 * x2 * x2 * x3 * x3 - d * x2 * x3 * x1 * x1 * x1 * y2 * y2 * y3 * y3 - d * x2 * y1 * x1 * x1 * x3 * x3 * y3 * y3 * y3 - d * x2 * y3 * x3 * x3 * y1 * y1 * y1 * y2 * y2 - d * x3 * y2 * x2 * x2 * y1 * y1 * y1 * y3 * y3 - d * y1 * y2 * x1 * x1 * x3 * x3 * x3 * y3 * y3 - d * y2 * y3 * x1 * x1 * x1 * x2 * x2 * x3 * x3 + d * x1 * x2 * x3 * y1 * y1 * y2 * y2 * y3 * y3 + d * x1 * y2 * y3 * x2 * x2 * x3 * x3 * y1 * y1 + d * x2 * y1 * y3 * x1 * x1 * x3 * x3 * y2 * y2 + d * x3 * y1 * y2 * x1 * x1 * x2 * x2 * y3 * y3 + x1 * y2 * d * d * x2 * x2 * x3 * x3 * y1 * y1 * y3 * y3 * y3 + x2 * y1 * d * d * x1 * x1 * x3 * x3 * y2 * y2 * y3 * y3 * y3 - x1 * x2 * d * d * x3 * x3 * x3 * y1 * y1 * y2 * y2 * y3 * y3 - y1 * y2 * d * d * x1 * x1 * x2 * x2 * x3 * x3 * x3 * y3 * y3) * h2 + (x1 * x2 * x3 + x1 * x3 * x2 * x2 * x2 + x1 * y2 * y3 + x2 * x3 * x1 * x1 * x1 + x2 * y1 * y3 + x3 * y1 * y2 + x3 * x1 * x1 * x1 * x2 * x2 * x2 + x3 * y1 * y1 * y1 * y2 * y2 * y2 + y1 * y3 * x2 * x2 * x2 + y2 * y3 * x1 * x1 * x1 - x1 * y3 * y2 * y2 * y2 - x2 * y3 * y1 * y1 * y1 - x3 * y1 * y2 * y2 * y2 - x3 * y2 * y1 * y1 * y1 - y3 * x1 * x1 * x1 * y2 * y2 * y2 - y3 * x2 * x2 * x2 * y1 * y1 * y1 + x1 * y2 * y3 * x2 * x2 + x1 * y3 * y1 * y1 * y2 * y2 * y2 + x2 * y1 * y3 * x1 * x1 + x2 * y3 * y1 * y1 * y1 * y2 * y2 + x3 * y1 * y2 * x1 * x1 + x3 * y1 * y2 * x2 * x2 + y1 * y3 * x1 * x1 * x2 * x2 * x2 + y2 * y3 * x1 * x1 * x1 * x2 * x2 - x1 * x2 * x3 * y1 * y1 - x1 * x2 * x3 * y2 * y2 - x1 * x3 * x2 * x2 * x2 * y1 * y1 - x1 * y2 * y3 * y1 * y1 - x2 * x3 * x1 * x1 * x1 * y2 * y2 - x2 * y1 * y3 * y2 * y2 - x3 * y1 * x1 * x1 * y2 * y2 * y2 - x3 * y2 * x2 * x2 * y1 * y1 * y1 + x1 * x2 * x3 * y1 * y1 * y2 * y2 + x3 * y1 * y2 * x1 * x1 * x2 * x2 - x1 * y2 * y3 * x2 * x2 * y1 * y1 - x2 * y1 * y3 * x1 * x1 * y2 * y2 + d * x1 * x2 * x3 * y1 * y1 * y2 * y2 + d * x3 * y1 * y2 * x1 * x1 * x2 * x2 - d * x1 * y2 * y3 * x2 * x2 * y1 * y1 - d * x2 * y1 * y3 * x1 * x1 * y2 * y2) * h3

private theorem edAdd_assoc_y_ring_gen {F : Type} [CommRing F] (d x1 y1 x2 y2 x3 y3 : F)
    (h1 : d * ((x1 * x1) * (y1 * y1)) = -(x1 * x1) + y1 * y1 - 1)
    (h2 : d * ((x2 * x2) * (y2 * y2)) = -(x2 * x2) + y2 * y2 - 1)
    (h3 : d * ((x3 * x3) * (y3 * y3)) = -(x3 * x3) + y3 * y3 - 1) :
        ((y1 * y2 + x1 * x2) * (1 + d * ((x1 * x2) * (y1 * y2))) * y3 + (x1 * y2 + y1 * x2) * (1 - d * ((x1 * x2) * (y1 * y2))) * x3) * ((1 + d * ((x2 * x3) * (y2 * y3))) * (1 - d * ((x2 * x3) * (y2 * y3))) - d * ((x1 * (x2 * y3 + y2 * x3)) * (y1 * (y2 * y3 + x2 * x3)))) =
            (y1 * (1 + d * ((x2 * x3) * (y2 * y3))) * (y2 * y3 + x2 * x3) + x1 * (1 - d * ((x2 * x3) * (y2 * y3))) * (x2 * y3 + y2 * x3)) * ((1 + d * ((x1 * x2) * (y1 * y2))) * (1 - d * ((x1 * x2) * (y1 * y2))) - d * (((x1 * y2 + y1 * x2) * x3) * ((y1 * y2 + x1 * x2) * y3))) := by
  linear_combination (d * x1 * x3 * x2 * x2 * y2 * y2 * y2 + d * x1 * y3 * x2 * x2 * x2 * y2 * y2 + d * x1 * x2 * x2 * x3 * x3 * x3 * y2 * y2 * y2 + d * x3 * y1 * x2 * x2 * x2 * y2 * y2 + d * y1 * y3 * x2 * x2 * y2 * y2 * y2 + d * y1 * x2 * x2 * x2 * x3 * x3 * x3 * y2 * y2 - d * x1 * x2 * x2 * x2 * y2 * y2 * y3 * y3 * y3 - d * y1 * x2 * x2 * y2 * y2 * y2 * y3 * y3 * y3 + d * x1 * x2 * y3 * x3 * x3 * y2 * y2 * y2 * y2 + d * y1 * y2 * y3 * x2 * x2 * x2 * x2 * x3 * x3 + x3 * y1 * d * d * x2 * x2 * x2 * y2 * y2 * y2 * y2 * y3 * y3 + y1 * y3 * d * d * x2 * x2 * x2 * x2 * x3 * x3 * y2 * y2 * y2 - d * x1 * x3 * y2 * x2 * x2 * x2 * x2 * y3 * y3 - d * x2 * x3 * y1 * y2 * y2 * y2 * y2 * y3 * y3 - x1 * x3 * d * d * x2 * x2 * x2 * x2 * y2 * y2 * y2 * y3 * y3 - x1 * y3 * d * d * x2 * x2 * x2 * x3 * x3 * y2 * y2 * y2 * y2) * h1 + (x1 * x2 * y3 * y3 * y3 + x2 * x3 * y1 * y1 * y1 + x2 * x1 * x1 * x1 * y3 * y3 * y3 + x2 * x3 * x3 * x3 * y1 * y1 * y1 + y1 * y2 * y3 * y3 * y3 + y2 * y3 * y1 * y1 * y1 - x1 * x2 * y3 - x1 * x3 * y2 - x1 * y2 * x3 * x3 * x3 - x2 * x3 * y1 - x2 * y1 * x3 * x3 * x3 - x2 * y3 * x1 * x1 * x1 - x3 * y2 * x1 * x1 * x1 - y1 * y2 * y3 - y2 * x1 * x1 * x1 * x3 * x3 * x3 - y2 * y1 * y1 * y1 * y3 * y3 * y3 + x1 * x2 * y3 * y1 * y1 + x1 * x3 * y2 * y1 * y1 + x1 * x3 * y2 * y3 * y3 + x1 * y2 * x3 * x3 * x3 * y1 * y1 + x2 * x3 * y1 * y3 * y3 + x3 * y2 * x1 * x1 * x1 * y3 * y3 + y1 * y2 * x1 * x1 * y3 * y3 * y3 + y2 * y3 * x3 * x3 * y1 * y1 * y1 - x1 * x2 * y3 * x3 * x3 - x1 * x2 * y1 * y1 * y3 * y3 * y3 - x2 * x3 * y1 * x1 * x1 - x2 * x3 * y1 * y1 * y1 * y3 * y3 - x2 * y1 * x1 * x1 * x3 * x3 * x3 - x2 * y3 * x1 * x1 * x1 * x3 * x3 - y1 * y2 * y3 * x1 * x1 - y1 * y2 * y3 * x3 * x3 + d * x2 * x3 * x3 * x3 * y1 * y1 * y1 * y3 * y3 + d * y2 * x3 * x3 * y1 * y1 * y1 * y3 * y3 * y3 + x1 * x2 * y3 * x3 * x3 * y1 * y1 + x2 * x3 * y1 * x1 * x1 * y3 * y3 - d * x1 * x2 * x3 * x3 * y3 * y3 * y3 - d * x1 * y2 * x3 * x3 * x3 * y3 * y3 - d * x2 * y1 * x3 * x3 * x3 * y3 * y3 - d * x2 * x1 * x1 * x1 * x3 * x3 * y3 * y3 * y3 - d * y1 * y2 * x3 * x3 * y3 * y3 * y3 - d * y2 * x1 * x1 * x1 * x3 * x3 * x3 * y3 * y3 - x1 * x3 * y2 * y1 * y1 * y3 * y3 - y1 * y2 * y3 * x1 * x1 * x3 * x3 + d * x1 * x2 * y3 * x3 * x3 * y2 * y2 + d * x1 * x2 * x3 * x3 * y1 * y1 * y3 * y3 * y3 + d * x1 * x3 * y2 * x2 * x2 * y3 * y3 + d * x1 * y2 * x3 * x3 * x3 * y1 * y1 * y3 * y3 + d * x2 * x3 * y1 * y1 * y1 * y2 * y2 * y3 * y3 + d * x2 * y3 * x1 * x1 * x1 * x3 * x3 * y2 * y2 + d * x3 * y2 * x1 * x1 * x1 * x2 * x2 * y3 * y3 + d * y2 * y3 * x2 * x2 * x3 * x3 * y1 * y1 * y1 - d * x2 * x3 * y1 * y2 * y2 * y3 * y3 - d * x2 * y1 * x1 * x1 * x3 * x3 * x3 * y3 * y3 - d * y1 * y2 * y3 * x2 * x2 * x3 * x3 - d * y1 * y2 * x1 * x1 * x3 * x3 * y3 * y3 * y3 + x1 * y2 * d * d * x2 * x2 * x3 * x3 * x3 * y1 * y1 * y3 * y3 + x2 * y1 * d * d * x1 * x1 * x3 * x3 * x3 * y2 * y2 * y3 * y3 - d * x1 * x2 * y3 * x3 * x3 * y1 * y1 * y2 * y2 - d * x1 * x3 * y2 * x2 * x2 * y1 * y1 * y3 * y3 - d * x2 * x3 * y1 * x1 * x1 * y2 * y2 * y3 * y3 - d * y1 * y2 * y3 * x1 * x1 * x2 * x2 * x3 * x3 - x1 * x2 * d * d * x3 * x3 * y1 * y1 * y2 * y2 * y3 * y3 * y3 - y1 * y2 * d * d * x1 * x1 * x2 * x2 * x3 * x3 * y3 * y3 * y3) * h2 + (x1 * x2 * y3 + x1 * x3 * y2 + x1 * y3 * x2 * x2 * x2 + x2 * x3 * y1 + x2 * y3 * x1 * x1 * x1 + x3 * y1 * x2 * x2 * x2 + x3 * y2 * x1 * x1 * x1 + y1 * y2 * y3 + y3 * x1 * x1 * x1 * x2 * x2 * x2 + y3 * y1 * y1 * y1 * y2 * y2 * y2 - x1 * x3 * y2 * y2 * y2 - x2 * x3 * y1 * y1 * y1 - x3 * x1 * x1 * x1 * y2 * y2 * y2 - x3 * x2 * x2 * x2 * y1 * y1 * y1 - y1 * y3 * y2 * y2 * y2 - y2 * y3 * y1 * y1 * y1 + x1 * x3 * y2 * x2 * x2 + x1 * x3 * y1 * y1 * y2 * y2 * y2 + x2 * x3 * y1 * x1 * x1 + x2 * x3 * y1 * y1 * y1 * y2 * y2 + x3 * y1 * x1 * x1 * x2 * x2 * x2 + x3 * y2 * x1 * x1 * x1 * x2 * x2 + y1 * y2 * y3 * x1 * x1 + y1 * y2 * y3 * x2 * x2 - x1 * x2 * y3 * y1 * y1 - x1 * x2 * y3 * y2 * y2 - x1 * x3 * y2 * y1 * y1 - x1 * y3 * x2 * x2 * x2 * y1 * y1 - x2 * x3 * y1 * y2 * y2 - x2 * y3 * x1 * x1 * x1 * y2 * y2 - y1 * y3 * x1 * x1 * y2 * y2 * y2 - y2 * y3 * x2 * x2 * y1 * y1 * y1 + x1 * x2 * y3 * y1 * y1 * y2 * y2 + y1 * y2 * y3 * x1 * x1 * x2 * x2 - x1 * x3 * y2 * x2 * x2 * y1 * y1 - x2 * x3 * y1 * x1 * x1 * y2 * y2 + d * x1 * x2 * y3 * y1 * y1 * y2 * y2 + d * y1 * y2 * y3 * x1 * x1 * x2 * x2 - d * x1 * x3 * y2 * x2 * x2 * y1 * y1 - d * x2 * x3 * y1 * x1 * x1 * y2 * y2) * h3

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
  exact @edAdd_assoc_x_ring_gen FpR Fp.commRing d x1 y1 x2 y2 x3 y3 h1 h2 h3

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
  exact @edAdd_assoc_y_ring_gen FpR Fp.commRing d x1 y1 x2 y2 x3 y3 h1 h2 h3

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

theorem edAdd_edSub_cancel {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    edSub (edAdd P Q) Q = P := by
  unfold edSub
  rw [edAdd_assoc hP hQ (edOnCurve_edNeg hQ), edAdd_edNeg_self hQ, edAdd_edZero hP]

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
end

section
section
set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational

open X25519Dalek
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards

theorem edToMontU_lt (P : EdPoint) : edToMontU P < p25519 := fpMul_lt _ _

theorem edToMontU_edExtToAffine {Q : EdExtPoint} (hZ : Q.Z % p25519 ≠ 0) :
    edToMontU (edExtToAffine Q) = fpMul (fpAdd Q.Z Q.Y) (fpInv (fpSub Q.Z Q.Y)) := by
  apply Fp.eq_of_ofNat_eq (edToMontU_lt _) (fpMul_lt _ _); unfold edToMontU edExtToAffine
  simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_fpInv, Fp.ofNat_one]
  have hz : Fp.ofNat Q.Z ≠ 0 := (Fp.ofNat_ne_zero_iff Q.Z).mpr hZ
  by_cases hzy : Fp.ofNat Q.Z - Fp.ofNat Q.Y = 0
  · (have h1 : (1 : Fp) - Fp.ofNat Q.Y * (Fp.ofNat Q.Z)⁻¹ = 0 := by grind); rw [hzy, h1, Lean.Grind.Field.inv_zero]; grind
  · grind

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational

end
end

section
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

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec

end
end

section
section
set_option autoImplicit false

namespace ProofLib

namespace ByteSlice

export X25519Dalek.ByteSlice (readLE slice)

theorem getD_slice (buf : List (BitVec 8)) (off n i : Nat) (d : BitVec 8) (h : i < n) :
    (slice buf off n).getD i d = buf.getD (off + i) d := by
  unfold X25519Dalek.ByteSlice.slice
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt h, List.getElem?_drop]

theorem readLE_succ (bs : List (BitVec 8)) (off n : Nat) :
    readLE bs off (n + 1) =
      readLE bs off n ||| (((bs.getD (off + n) 0#8).zeroExtend 64) <<< (8 * n)) := rfl

private theorem pack64_eq_or (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    pack64 b0 b1 b2 b3 b4 b5 b6 b7 =
      0#64 ||| (b0.zeroExtend 64 <<< (8 * 0)) ||| (b1.zeroExtend 64 <<< (8 * 1))
        ||| (b2.zeroExtend 64 <<< (8 * 2)) ||| (b3.zeroExtend 64 <<< (8 * 3))
        ||| (b4.zeroExtend 64 <<< (8 * 4)) ||| (b5.zeroExtend 64 <<< (8 * 5))
        ||| (b6.zeroExtend 64 <<< (8 * 6)) ||| (b7.zeroExtend 64 <<< (8 * 7)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack64, BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem pack64_eq_readLE_8 (bs : List (BitVec 8)) (off : Nat) :
    pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
      (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)
      (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
      (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8) =
      readLE bs off 8 := by
  rw [pack64_eq_or]
  rfl

end ByteSlice

end ProofLib

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase

export X25519Dalek (a24 fe51Val fe51ValOfBytes ed25519BasepointTableBytes)

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.RoTables

open ProofLib

theorem readLE_cons8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (rest : List (BitVec 8)) (off n : Nat) :
    ByteSlice.readLE (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) (off + 8) n =
    ByteSlice.readLE rest off n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ByteSlice.readLE_succ, ByteSlice.readLE_succ, ih,
      show off + 8 + n = (off + n) + 8 by omega]
    rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.RoTables

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs

open ProofLib
open X25519Dalek

export X25519Dalek (scalarRadix16Digits fe51ValAt edProjDouble edAddAffineNiels edAsProjective
  edAsExtended edDouble4 edTableEntryAt edSelectAffineNiels edMulBaseStep edMulBaseStepAt
  edMulBaseLoopWith edMulBaseLoop edMulBase edExtToMontgomeryU)

private theorem scalarRadix16Digits_go_length (a_bs : List (BitVec 8)) :
    ∀ (idx : Nat) (carry : Int) (acc : List (BitVec 8)),
      (X25519Dalek.scalarRadix16Digits.go a_bs idx carry acc).length = acc.length + idx
  | 0, _, acc => by simp [X25519Dalek.scalarRadix16Digits.go]
  | k + 1, carry, acc => by
    unfold X25519Dalek.scalarRadix16Digits.go
    dsimp only
    split <;> simp only [scalarRadix16Digits_go_length, List.length_cons] <;> omega

theorem scalarRadix16Digits_length (a_bs : List (BitVec 8)) :
    (scalarRadix16Digits a_bs).length = 64 := by
  simpa [scalarRadix16Digits] using scalarRadix16Digits_go_length a_bs 64 0 []

theorem readLE_congr_off (bs bs' : List (BitVec 8)) (off1 off2 n : Nat)
    (h : ∀ i, i < n → bs.getD (off1 + i) 0#8 = bs'.getD (off2 + i) 0#8) :
    ByteSlice.readLE bs off1 n = ByteSlice.readLE bs' off2 n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [ByteSlice.readLE_succ, ih (fun i hi => h i (by omega)), h k (by omega)]

theorem readLE_slice_eq (bs : List (BitVec 8)) (off m k : Nat)
    (h1 : decide (k + 8 ≤ m) = true) :
    ByteSlice.readLE (ProofLib.ByteSlice.slice bs off m) k 8 = ByteSlice.readLE bs (off + k) 8 := by
  have hk : k + 8 ≤ m := of_decide_eq_true h1
  apply readLE_congr_off
  intro i hi
  rw [ByteSlice.getD_slice bs off m (k + i) 0#8 (by omega), Nat.add_assoc]

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs

end
end

section
section
/-!
# Curve Coordinate Models & Basepoint Table Checker, Part 1 (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.ScalarMul1`)

Pure `0-sorry` mathematical bridge proofs for `.rodata` `AffineNiels` extraction, `ProjectivePoint`,
`CompletedPoint`, `edDouble3`, `edDouble4`, `edPointEq`, `AffineNiels`, and `ProjectiveNiels`.
-/

set_option autoImplicit false


namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.ScalarMul1

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open ProofLib
open X25519Dalek
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.RoTables
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards
attribute [local irreducible] fpInv fpPow recoverXEven

theorem getD_readWords64 {bs : List (BitVec 8)} {n k : Nat}
    (hlen : (readWords64 bs n).length = n) (hk : k < n) :
    (readWords64 bs n).getD k 0#64 = ByteSlice.readLE bs (8 * k) 8 := by
  induction n generalizing bs k with
  | zero => omega
  | succ n ih =>
    unfold readWords64 at hlen ⊢
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      try (simp at hlen; done)
    simp only [List.length_cons] at hlen
    rcases k with _ | k
    · simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.mul_zero, Nat.zero_add,
        ← ByteSlice.pack64_eq_readLE_8]
    · change (readWords64 rest n).getD k 0#64 = _
      rw [@ih rest k (by omega) (by omega), show 8 * (k + 1) = 8 * k + 8 by omega, readLE_cons8]

theorem fe51ValsFromWords_length_imp {ws : List (BitVec 64)} {n : Nat}
    (hlen : (fe51ValsFromWords ws n).length = n) :
    5 * n ≤ ws.length := by
  induction n generalizing ws with
  | zero => omega
  | succ n ih =>
    unfold fe51ValsFromWords at hlen
    rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, rest⟩⟩⟩⟩⟩ <;>
      try (simp at hlen; done)
    simp only [List.length_cons] at hlen ⊢
    have := @ih rest (by omega)
    omega

theorem getD_fe51ValsFromWords {ws : List (BitVec 64)} {n k : Nat}
    (hlen : (fe51ValsFromWords ws n).length = n) (hk : k < n) :
    (fe51ValsFromWords ws n).getD k 0 =
      fe51Val (ws.getD (5 * k) 0#64) (ws.getD (5 * k + 1) 0#64)
        (ws.getD (5 * k + 2) 0#64) (ws.getD (5 * k + 3) 0#64)
        (ws.getD (5 * k + 4) 0#64) % p25519 := by
  induction n generalizing ws k with
  | zero => omega
  | succ n ih =>
    unfold fe51ValsFromWords at hlen ⊢
    rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, rest⟩⟩⟩⟩⟩ <;>
      try (simp at hlen; done)
    simp only [List.length_cons] at hlen
    rcases k with _ | k
    · simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.mul_zero, Nat.zero_add]
    · change (fe51ValsFromWords rest n).getD k 0 = _
      rw [@ih rest k (by omega) (by omega), show 5 * (k + 1) = 5 * k + 5 by omega]
      simp only [List.getD_cons_succ]

theorem nielsFromVals_length_imp {vs : List Nat} {m : Nat}
    (hlen : (nielsFromVals vs m).length = m) :
    3 * m ≤ vs.length := by
  induction m generalizing vs with
  | zero => omega
  | succ m ih =>
    unfold nielsFromVals at hlen
    rcases vs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, rest⟩⟩⟩ <;>
      try (simp at hlen; done)
    simp only [List.length_cons] at hlen ⊢
    have := @ih rest (by omega)
    omega

theorem getD_nielsFromVals {vs : List Nat} {m k : Nat}
    (hlen : (nielsFromVals vs m).length = m) (hk : k < m) :
    (nielsFromVals vs m).getD k (0, 0, 0) =
      (vs.getD (3 * k) 0, vs.getD (3 * k + 1) 0, vs.getD (3 * k + 2) 0) := by
  induction m generalizing vs k with
  | zero => omega
  | succ m ih =>
    unfold nielsFromVals at hlen ⊢
    rcases vs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, rest⟩⟩⟩ <;>
      try (simp at hlen; done)
    simp only [List.length_cons] at hlen
    rcases k with _ | k
    · simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.mul_zero, Nat.zero_add]
    · change (nielsFromVals rest m).getD k (0, 0, 0) = _
      rw [@ih rest k (by omega) (by omega), show 3 * (k + 1) = 3 * k + 3 by omega]
      simp only [List.getD_cons_succ]

theorem readWords64_length_le (bs : List (BitVec 8)) (n : Nat) :
    (readWords64 bs n).length ≤ n := by
  induction n generalizing bs with
  | zero => simp [readWords64]
  | succ n ih =>
    unfold readWords64
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [List.length_nil, List.length_cons, Nat.zero_le]
    have := ih rest
    omega

theorem fe51ValsFromWords_length_le (ws : List (BitVec 64)) (n : Nat) :
    (fe51ValsFromWords ws n).length ≤ n := by
  induction n generalizing ws with
  | zero => simp [fe51ValsFromWords]
  | succ n ih =>
    unfold fe51ValsFromWords
    rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, rest⟩⟩⟩⟩⟩ <;>
      simp only [List.length_nil, List.length_cons, Nat.zero_le]
    have := ih rest
    omega

theorem getD_nielsFromBytes {bs : List (BitVec 8)} {m idx : Nat}
    (hlen : (nielsFromBytes bs m).length = m) (hidx : idx < m) :
    (nielsFromBytes bs m).getD idx (0, 0, 0) =
      (fe51ValAt bs (120 * idx) % p25519,
       fe51ValAt bs (120 * idx + 40) % p25519,
       fe51ValAt bs (120 * idx + 80) % p25519) := by
  unfold nielsFromBytes at hlen ⊢
  let ws := readWords64 bs (15 * m)
  let vs := fe51ValsFromWords ws (3 * m)
  have hvs_le : vs.length ≤ 3 * m := fe51ValsFromWords_length_le ws (3 * m)
  have hvs_ge : 3 * m ≤ vs.length := nielsFromVals_length_imp hlen
  have hvs_len : vs.length = 3 * m := by omega
  have hws_le : ws.length ≤ 15 * m := readWords64_length_le bs (15 * m)
  have hws_ge : 5 * (3 * m) ≤ ws.length := fe51ValsFromWords_length_imp hvs_len
  have hws_len : ws.length = 15 * m := by omega
  rw [getD_nielsFromVals hlen hidx]
  have hval (r : Nat) (hr : r < 3 * m) :
      vs.getD r 0 = fe51ValAt bs (40 * r) % p25519 := by
    rw [getD_fe51ValsFromWords hvs_len hr,
        getD_readWords64 hws_len (by omega),
        getD_readWords64 hws_len (by omega),
        getD_readWords64 hws_len (by omega),
        getD_readWords64 hws_len (by omega),
        getD_readWords64 hws_len (by omega)]
    unfold fe51ValAt
    rw [show 8 * (5 * r) = 40 * r by omega,
        show 8 * (5 * r + 1) = 40 * r + 8 by omega,
        show 8 * (5 * r + 2) = 40 * r + 16 by omega,
        show 8 * (5 * r + 3) = 40 * r + 24 by omega,
        show 8 * (5 * r + 4) = 40 * r + 32 by omega]
  rw [hval (3 * idx) (by omega), hval (3 * idx + 1) (by omega), hval (3 * idx + 2) (by omega),
      show 40 * (3 * idx) = 120 * idx by omega,
      show 40 * (3 * idx + 1) = 120 * idx + 40 by omega,
      show 40 * (3 * idx + 2) = 120 * idx + 80 by omega]

theorem fe51ValAt_slice_eq (bs : List (BitVec 8)) (base len off : Nat)
    (h : off + 40 ≤ len) :
    fe51ValAt (ProofLib.ByteSlice.slice bs base len) off = fe51ValAt bs (base + off) := by
  unfold fe51ValAt
  rw [readLE_slice_eq bs base len off (by rw [decide_eq_true_eq]; omega),
      readLE_slice_eq bs base len (off + 8) (by rw [decide_eq_true_eq]; omega),
      readLE_slice_eq bs base len (off + 16) (by rw [decide_eq_true_eq]; omega),
      readLE_slice_eq bs base len (off + 24) (by rw [decide_eq_true_eq]; omega),
      readLE_slice_eq bs base len (off + 32) (by rw [decide_eq_true_eq]; omega)]
  simp only [Nat.add_assoc]

/-! ## 2. Coordinate Models (`edExtNeg`, `EdProjValid`, `EdCompValid`, `edProjDouble`, `Niels`) -/

/-- Projective point validity `(X : Y : Z)` (`T` ignored): `Z ≢ 0 (mod p)` and `(X/Z, Y/Z)` lies
    on the twisted Edwards curve. -/
structure EdProjValid (P : EdExtPoint) : Prop where
  z_ne_zero : Fp.ofNat P.Z ≠ 0
  on_curve : edOnCurve (edExtToAffine P) = true

theorem edProjValid_of_edExtValid {P : EdExtPoint} (hP : EdExtValid P) : EdProjValid P :=
  ⟨hP.z_ne_zero, hP.on_curve⟩

/-- Affine projection $(X Z^{-1} \bmod p, Y T^{-1} \bmod p)$ of a `CompletedPoint`
    $((X : Z), (Y : T)) \in \mathbb{P}^1 \times \mathbb{P}^1$. -/
def edCompToAffine (C : EdExtPoint) : EdPoint :=
  ⟨fpMul C.X (fpInv C.Z), fpMul C.Y (fpInv C.T)⟩

/-- Validity invariant for a `CompletedPoint` $((X : Z), (Y : T))$: $Z \not\equiv 0$,
    $T \not\equiv 0$, and $(X Z^{-1}, Y T^{-1})$ lies on the curve. -/
structure EdCompValid (C : EdExtPoint) : Prop where
  z_ne_zero : Fp.ofNat C.Z ≠ 0
  t_ne_zero : Fp.ofNat C.T ≠ 0
  on_curve : edOnCurve (edCompToAffine C) = true

theorem edCompToAffine_x_lt (C : EdExtPoint) : (edCompToAffine C).x < p25519 := fpMul_lt _ _
theorem edCompToAffine_y_lt (C : EdExtPoint) : (edCompToAffine C).y < p25519 := fpMul_lt _ _

theorem edCompToAffine_fp_x (C : EdExtPoint) :
    Fp.ofNat (edCompToAffine C).x = Fp.ofNat C.X * (Fp.ofNat C.Z)⁻¹ := by
  unfold edCompToAffine; simp

theorem edCompToAffine_fp_y (C : EdExtPoint) :
    Fp.ofNat (edCompToAffine C).y = Fp.ofNat C.Y * (Fp.ofNat C.T)⁻¹ := by
  unfold edCompToAffine; simp

theorem edAsExtended_toAffine {C : EdExtPoint} (hC : EdCompValid C) :
    edExtToAffine (edAsExtended C) = edCompToAffine C := by
  have hZ := hC.z_ne_zero
  have hT := hC.t_ne_zero
  ext
  · apply Fp.eq_of_ofNat_eq (edExtToAffine_x_lt _) (edCompToAffine_x_lt _)
    rw [edExtToAffine_fp_x, edCompToAffine_fp_x]
    unfold edAsExtended
    simp only [Fp.ofNat_fpMul]
    grind
  · apply Fp.eq_of_ofNat_eq (edExtToAffine_y_lt _) (edCompToAffine_y_lt _)
    rw [edExtToAffine_fp_y, edCompToAffine_fp_y]
    unfold edAsExtended
    simp only [Fp.ofNat_fpMul]
    grind

theorem edExtValid_edAsExtended {C : EdExtPoint} (hC : EdCompValid C) :
    EdExtValid (edAsExtended C) where
  z_ne_zero := by
    unfold edAsExtended
    simp only [Fp.ofNat_fpMul]
    exact Fp.mul_ne_zero hC.z_ne_zero hC.t_ne_zero
  tz_eq_xy := by
    unfold edAsExtended
    simp only [Fp.ofNat_fpMul]
    grind
  on_curve := by
    rw [edAsExtended_toAffine hC]
    exact hC.on_curve

theorem edAsProjective_toAffine (C : EdExtPoint) :
    edExtToAffine (edAsProjective C) = edExtToAffine (edAsExtended C) := rfl

theorem edProjValid_edAsProjective {C : EdExtPoint} (hC : EdCompValid C) :
    EdProjValid (edAsProjective C) where
  z_ne_zero := (edExtValid_edAsExtended hC).z_ne_zero
  on_curve := by
    rw [edAsProjective_toAffine, edAsExtended_toAffine hC]
    exact hC.on_curve

private theorem edProjDouble_zt_ring (d X Y Z x y : Fp)
    (hZ : Z ≠ 0) (hx : x = X * Z⁻¹) (hy : y = Y * Z⁻¹)
    (hcurve : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hdp : 1 + d * ((x * x) * (y * y)) ≠ 0)
    (hdm : 1 - d * ((x * x) * (y * y)) ≠ 0) :
    (Y * Y - X * X ≠ 0) ∧
    ((Z * Z + Z * Z) - (Y * Y - X * X) ≠ 0) ∧
    (((X + Y) * (X + Y) - (X * X + Y * Y)) * (Y * Y - X * X)⁻¹ =
      (x * y + y * x) * (1 + d * ((x * x) * (y * y)))⁻¹) ∧
    ((X * X + Y * Y) * ((Z * Z + Z * Z) - (Y * Y - X * X))⁻¹ =
      (y * y + x * x) * (1 - d * ((x * x) * (y * y)))⁻¹) := by
  have hZZ : Y * Y - X * X = Z * Z * (1 + d * ((x * x) * (y * y))) := by grind
  have hTT : (Z * Z + Z * Z) - (Y * Y - X * X) = Z * Z * (1 - d * ((x * x) * (y * y))) := by grind
  have hZ_ne : Y * Y - X * X ≠ 0 := by
    rw [hZZ]; exact Fp.mul_ne_zero (Fp.mul_ne_zero hZ hZ) hdp
  have hT_ne : (Z * Z + Z * Z) - (Y * Y - X * X) ≠ 0 := by
    rw [hTT]; exact Fp.mul_ne_zero (Fp.mul_ne_zero hZ hZ) hdm
  refine ⟨hZ_ne, hT_ne, ?_, ?_⟩ <;> grind

theorem edProjDouble_toAffine {P : EdExtPoint} (hP : EdProjValid P) :
    edCompToAffine (edProjDouble P.X P.Y P.Z) = edAdd (edExtToAffine P) (edExtToAffine P) := by
  have hcurve := edOnCurve_fp_eq hP.on_curve
  have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hP.on_curve
  have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hP.on_curve
  obtain ⟨_, _, hx_eq, hy_eq⟩ := edProjDouble_zt_ring
    (Fp.ofNat edD) (Fp.ofNat P.X) (Fp.ofNat P.Y) (Fp.ofNat P.Z)
    (Fp.ofNat (edExtToAffine P).x) (Fp.ofNat (edExtToAffine P).y)
    hP.z_ne_zero (edExtToAffine_fp_x P) (edExtToAffine_fp_y P) hcurve hdp hdm
  ext
  · apply Fp.eq_of_ofNat_eq (edCompToAffine_x_lt _) (edAdd_x_lt _ _)
    rw [edCompToAffine_fp_x, edAdd_fp_x]
    unfold edProjDouble
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpSq, Fp.ofNat_mod]
    exact hx_eq
  · apply Fp.eq_of_ofNat_eq (edCompToAffine_y_lt _) (edAdd_y_lt _ _)
    rw [edCompToAffine_fp_y, edAdd_fp_y]
    unfold edProjDouble
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpSq, Fp.ofNat_mod]
    exact hy_eq

theorem edCompValid_edProjDouble {P : EdExtPoint} (hP : EdProjValid P) :
    EdCompValid (edProjDouble P.X P.Y P.Z) where
  z_ne_zero := by
    have hcurve := edOnCurve_fp_eq hP.on_curve
    have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hP.on_curve
    have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hP.on_curve
    unfold edProjDouble
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpSq, Fp.ofNat_mod]
    exact (edProjDouble_zt_ring _ _ _ _ _ _
      hP.z_ne_zero (edExtToAffine_fp_x P) (edExtToAffine_fp_y P) hcurve hdp hdm).1
  t_ne_zero := by
    have hcurve := edOnCurve_fp_eq hP.on_curve
    have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hP.on_curve
    have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hP.on_curve
    unfold edProjDouble
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpSq, Fp.ofNat_mod]
    exact (edProjDouble_zt_ring _ _ _ _ _ _
      hP.z_ne_zero (edExtToAffine_fp_x P) (edExtToAffine_fp_y P) hcurve hdp hdm).2.1
  on_curve := by
    rw [edProjDouble_toAffine hP]
    exact edOnCurve_edAdd hP.on_curve hP.on_curve


theorem edDouble4_spec {P : EdExtPoint} (hP : EdExtValid P) :
    EdExtValid (edDouble4 P) ∧
    edExtToAffine (edDouble4 P) = edNatSmul 16 (edExtToAffine P) := by
  unfold edDouble4
  let C1 := edProjDouble P.X P.Y P.Z
  have hC1 : EdCompValid C1 := edCompValid_edProjDouble (edProjValid_of_edExtValid hP)
  let P1 := edAsProjective C1
  have hP1 : EdProjValid P1 := edProjValid_edAsProjective hC1
  let C2 := edProjDouble P1.X P1.Y P1.Z
  have hC2 : EdCompValid C2 := edCompValid_edProjDouble hP1
  let P2 := edAsProjective C2
  have hP2 : EdProjValid P2 := edProjValid_edAsProjective hC2
  let C3 := edProjDouble P2.X P2.Y P2.Z
  have hC3 : EdCompValid C3 := edCompValid_edProjDouble hP2
  let P3 := edAsProjective C3
  have hP3 : EdProjValid P3 := edProjValid_edAsProjective hC3
  let C4 := edProjDouble P3.X P3.Y P3.Z
  have hC4 : EdCompValid C4 := edCompValid_edProjDouble hP3
  refine ⟨edExtValid_edAsExtended hC4, ?_⟩
  have h1 : edExtToAffine P1 = edNatSmul 2 (edExtToAffine P) := by
    rw [edAsProjective_toAffine, edAsExtended_toAffine hC1, edProjDouble_toAffine (edProjValid_of_edExtValid hP),
        edNatSmul_two hP.on_curve]
  have h2 : edExtToAffine P2 = edNatSmul 4 (edExtToAffine P) := by
    rw [edAsProjective_toAffine, edAsExtended_toAffine hC2, edProjDouble_toAffine hP1, h1,
        ← edNatSmul_two (edOnCurve_edNatSmul 2 hP.on_curve),
        ← edNatSmul_mul 2 2 hP.on_curve]
  have h3 : edExtToAffine P3 = edNatSmul 8 (edExtToAffine P) := by
    rw [edAsProjective_toAffine, edAsExtended_toAffine hC3, edProjDouble_toAffine hP2, h2,
        ← edNatSmul_two (edOnCurve_edNatSmul 4 hP.on_curve),
        ← edNatSmul_mul 2 4 hP.on_curve]
  rw [edAsExtended_toAffine hC4, edProjDouble_toAffine hP3, h3,
      ← edNatSmul_two (edOnCurve_edNatSmul 8 hP.on_curve),
      ← edNatSmul_mul 2 8 hP.on_curve]


/-! ## 3. `AffineNiels` & `ProjectiveNiels` Point Addition and Subtraction -/

/-- `AffineNielsPoint` `(ypx, ymx, xy2d)` represents curve point `Q = (x, y)` over `Fp`. -/
structure EdAffineNielsValid (ypx ymx xy2d : Nat) (Q : EdPoint) : Prop where
  on_curve : edOnCurve Q = true
  ypx_eq : Fp.ofNat ypx = Fp.ofNat Q.y + Fp.ofNat Q.x
  ymx_eq : Fp.ofNat ymx = Fp.ofNat Q.y - Fp.ofNat Q.x
  xy2d_eq : Fp.ofNat xy2d = 2 * Fp.ofNat edD * Fp.ofNat Q.x * Fp.ofNat Q.y

theorem edAffineNielsValid_edZero : EdAffineNielsValid 1 1 0 edZero where
  on_curve := edOnCurve_edZero
  ypx_eq := by simp [edZero]; grind
  ymx_eq := by simp [edZero]; grind
  xy2d_eq := by simp [edZero]; grind

theorem edAffineNielsValid_neg {ypx ymx xy2d : Nat} {Q : EdPoint}
    (h : EdAffineNielsValid ypx ymx xy2d Q) :
    EdAffineNielsValid ymx ypx (fpNeg xy2d) (edNeg Q) where
  on_curve := edOnCurve_edNeg h.on_curve
  ypx_eq := by rw [h.ymx_eq]; simp only [edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod]; grind
  ymx_eq := by rw [h.ypx_eq]; simp only [edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod]; grind
  xy2d_eq := by rw [Fp.ofNat_fpNeg, h.xy2d_eq]; simp only [edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod]; grind

private theorem edAddAffineNiels_ring (d X1 Y1 Z1 T1 x1 y1 x2 y2 ypx ymx xy2d : Fp)
    (h2 : (2 : Fp) ≠ 0) (hZ1 : Z1 ≠ 0) (hT1 : T1 * Z1 = X1 * Y1)
    (hx1 : x1 = X1 * Z1⁻¹) (hy1 : y1 = Y1 * Z1⁻¹)
    (hypx : ypx = y2 + x2) (hymx : ymx = y2 - x2) (hxy2d : xy2d = 2 * d * x2 * y2)
    (hdp : 1 + d * ((x1 * x2) * (y1 * y2)) ≠ 0)
    (hdm : 1 - d * ((x1 * x2) * (y1 * y2)) ≠ 0) :
    let PP := (X1 + Y1) * ypx
    let MM := (Y1 - X1) * ymx
    let TT2d := T1 * xy2d
    let ZZ2 := Z1 + Z1
    (TT2d + ZZ2 ≠ 0) ∧
    (ZZ2 - TT2d ≠ 0) ∧
    ((PP - MM) * (TT2d + ZZ2)⁻¹ = (x1 * y2 + y1 * x2) * (1 + d * ((x1 * x2) * (y1 * y2)))⁻¹) ∧
    ((MM + PP) * (ZZ2 - TT2d)⁻¹ = (y1 * y2 + x1 * x2) * (1 - d * ((x1 * x2) * (y1 * y2)))⁻¹) := by
  have hZ : T1 * xy2d + (Z1 + Z1) = 2 * Z1 * (1 + d * ((x1 * x2) * (y1 * y2))) := by grind
  have hT : (Z1 + Z1) - T1 * xy2d = 2 * Z1 * (1 - d * ((x1 * x2) * (y1 * y2))) := by grind
  have hZ_ne : T1 * xy2d + (Z1 + Z1) ≠ 0 := by
    rw [hZ]; exact Fp.mul_ne_zero (Fp.mul_ne_zero h2 hZ1) hdp
  have hT_ne : (Z1 + Z1) - T1 * xy2d ≠ 0 := by
    rw [hT]; exact Fp.mul_ne_zero (Fp.mul_ne_zero h2 hZ1) hdm
  refine ⟨hZ_ne, hT_ne, ?_, ?_⟩ <;> grind

theorem edAddAffineNiels_toAffine {P : EdExtPoint} {ypx ymx xy2d : Nat} {Q : EdPoint}
    (hP : EdExtValid P) (hQ : EdAffineNielsValid ypx ymx xy2d Q) :
    edCompToAffine (edAddAffineNiels P ypx ymx xy2d) = edAdd (edExtToAffine P) Q := by
  have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hQ.on_curve
  have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hQ.on_curve
  obtain ⟨_, _, hx_eq, hy_eq⟩ := edAddAffineNiels_ring
    (Fp.ofNat edD) (Fp.ofNat P.X) (Fp.ofNat P.Y) (Fp.ofNat P.Z) (Fp.ofNat P.T)
    (Fp.ofNat (edExtToAffine P).x) (Fp.ofNat (edExtToAffine P).y)
    (Fp.ofNat Q.x) (Fp.ofNat Q.y) (Fp.ofNat ypx) (Fp.ofNat ymx) (Fp.ofNat xy2d)
    Fp.two_ne_zero hP.z_ne_zero hP.tz_eq_xy
    (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
    hQ.ypx_eq hQ.ymx_eq hQ.xy2d_eq hdp hdm
  ext
  · apply Fp.eq_of_ofNat_eq (edCompToAffine_x_lt _) (edAdd_x_lt _ _)
    rw [edCompToAffine_fp_x, edAdd_fp_x]
    unfold edAddAffineNiels
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpMul]
    exact hx_eq
  · apply Fp.eq_of_ofNat_eq (edCompToAffine_y_lt _) (edAdd_y_lt _ _)
    rw [edCompToAffine_fp_y, edAdd_fp_y]
    unfold edAddAffineNiels
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpMul]
    exact hy_eq

theorem edCompValid_edAddAffineNiels {P : EdExtPoint} {ypx ymx xy2d : Nat} {Q : EdPoint}
    (hP : EdExtValid P) (hQ : EdAffineNielsValid ypx ymx xy2d Q) :
    EdCompValid (edAddAffineNiels P ypx ymx xy2d) where
  z_ne_zero := by
    have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hQ.on_curve
    have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hQ.on_curve
    unfold edAddAffineNiels
    simp only [Fp.ofNat_fpAdd, Fp.ofNat_fpMul]
    exact (edAddAffineNiels_ring _ _ _ _ _ _ _ _ _ _ _ _
      Fp.two_ne_zero hP.z_ne_zero hP.tz_eq_xy
      (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
      hQ.ypx_eq hQ.ymx_eq hQ.xy2d_eq hdp hdm).1
  t_ne_zero := by
    have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hQ.on_curve
    have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hQ.on_curve
    unfold edAddAffineNiels
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpMul]
    exact (edAddAffineNiels_ring _ _ _ _ _ _ _ _ _ _ _ _
      Fp.two_ne_zero hP.z_ne_zero hP.tz_eq_xy
      (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
      hQ.ypx_eq hQ.ymx_eq hQ.xy2d_eq hdp hdm).2.1
  on_curve := by
    rw [edAddAffineNiels_toAffine hP hQ]
    exact edOnCurve_edAdd hP.on_curve hQ.on_curve


end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.ScalarMul1

end
end

section
section
/-!
# Signed Scalar Multiplication & Radix-16 Basepoint Bridge, Part 2 (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.ScalarMul2`)

Pure `0-sorry` mathematical bridge proofs for `edIntSmul`, `ed25519BasepointTableBytes` soundness,
`scalarRadix16Digits`, and `edMulBase` equivalence to `edSmul`.
-/

set_option autoImplicit false


namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.ScalarMul2

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open ProofLib
open X25519Dalek
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.ScalarMul1
attribute [local irreducible] fpInv fpPow recoverXEven

/-! ## 4. Signed Integer Scalar Multiplication (`edIntSmul`) & Table Selection -/

/-- Signed integer scalar multiplication $[z]P$ on affine twisted Edwards points. -/
def edIntSmul (z : Int) (P : EdPoint) : EdPoint :=
  if z ≥ 0 then edNatSmul z.toNat P
  else edNeg (edNatSmul (-z).toNat P)

theorem edOnCurve_edIntSmul (z : Int) {P : EdPoint} (hP : edOnCurve P = true) :
    edOnCurve (edIntSmul z P) = true := by
  unfold edIntSmul
  split
  · exact edOnCurve_edNatSmul _ hP
  · exact edOnCurve_edNeg (edOnCurve_edNatSmul _ hP)

@[simp] theorem edIntSmul_zero (P : EdPoint) : edIntSmul 0 P = edZero := rfl

@[simp] theorem edIntSmul_ofNat (n : Nat) (P : EdPoint) :
    edIntSmul (Int.ofNat n) P = edNatSmul n P := by
  unfold edIntSmul
  have h : Int.ofNat n ≥ 0 := by change (n : Int) ≥ 0; omega
  have ht : (Int.ofNat n).toNat = n := rfl
  simp only [h, ↓reduceIte, ht]

@[simp] private theorem edIntSmul_natCast (n : Nat) (P : EdPoint) :
    edIntSmul (n : Int) P = edNatSmul n P :=
  edIntSmul_ofNat n P

theorem edNatSmul_edNeg (n : Nat) (P : EdPoint) :
    edNatSmul n (edNeg P) = edNeg (edNatSmul n P) := by
  induction n with
  | zero => simp
  | succ k ih => rw [edNatSmul_succ, edNatSmul_succ, ih, edNeg_edAdd]

theorem edIntSmul_neg (z : Int) {P : EdPoint} (hP : edOnCurve P = true) :
    edIntSmul (-z) P = edNeg (edIntSmul z P) := by
  unfold edIntSmul
  rcases Int.lt_trichotomy z 0 with hlt | rfl | hgt
  · have h1 : -z ≥ 0 := by omega
    have h2 : ¬(z ≥ 0) := by omega
    simp only [h1, h2, ↓reduceIte]
    rw [edNeg_edNeg (edOnCurve_edNatSmul _ hP)]
  · simp
  · have h1 : ¬(-z ≥ 0) := by omega
    have h2 : z ≥ 0 := by omega
    simp only [h1, h2, ↓reduceIte, Int.neg_neg]

theorem edIntSmul_edNeg (z : Int) {P : EdPoint} (hP : edOnCurve P = true) :
    edIntSmul z (edNeg P) = edNeg (edIntSmul z P) := by
  unfold edIntSmul
  split
  · exact edNatSmul_edNeg _ P
  · rw [edNatSmul_edNeg, edNeg_edNeg (edOnCurve_edNatSmul _ hP)]

theorem edNatSmul_sub {m n : Nat} (h : n ≤ m) {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul (m - n) P = edAdd (edNatSmul m P) (edNeg (edNatSmul n P)) := by
  have hm : m = (m - n) + n := by omega
  conv => rhs; arg 1; rw [hm]
  rw [edNatSmul_add (m - n) n hP]
  exact (edAdd_edSub_cancel (edOnCurve_edNatSmul (m - n) hP) (edOnCurve_edNatSmul n hP)).symm

theorem edIntSmul_add (a b : Int) {P : EdPoint} (hP : edOnCurve P = true) :
    edIntSmul (a + b) P = edAdd (edIntSmul a P) (edIntSmul b P) := by
  by_cases ha : a ≥ 0
  · by_cases hb : b ≥ 0
    · have hab : a + b ≥ 0 := by omega
      unfold edIntSmul
      simp only [ha, hb, hab, ↓reduceIte]
      rw [show (a + b).toNat = a.toNat + b.toNat by omega, edNatSmul_add _ _ hP]
    · by_cases hab : a + b ≥ 0
      · unfold edIntSmul
        simp only [ha, hb, hab, ↓reduceIte]
        have hle : (-b).toNat ≤ a.toNat := by omega
        rw [show (a + b).toNat = a.toNat - (-b).toNat by omega]
        exact edNatSmul_sub hle hP
      · unfold edIntSmul
        simp only [ha, hb, hab, ↓reduceIte]
        have hle : a.toNat ≤ (-b).toNat := by omega
        rw [show (-(a + b)).toNat = (-b).toNat - a.toNat by omega,
            edNatSmul_sub hle hP, edNeg_edAdd,
            edNeg_edNeg (edOnCurve_edNatSmul _ hP), edAdd_comm]
  · by_cases hb : b ≥ 0
    · by_cases hab : a + b ≥ 0
      · unfold edIntSmul
        simp only [ha, hb, hab, ↓reduceIte]
        have hle : (-a).toNat ≤ b.toNat := by omega
        rw [show (a + b).toNat = b.toNat - (-a).toNat by omega,
            edNatSmul_sub hle hP, edAdd_comm]
      · unfold edIntSmul
        simp only [ha, hb, hab, ↓reduceIte]
        have hle : b.toNat ≤ (-a).toNat := by omega
        rw [show (-(a + b)).toNat = (-a).toNat - b.toNat by omega,
            edNatSmul_sub hle hP, edNeg_edAdd,
            edNeg_edNeg (edOnCurve_edNatSmul _ hP)]
    · have hab : ¬(a + b ≥ 0) := by omega
      unfold edIntSmul
      simp only [ha, hb, hab, ↓reduceIte]
      rw [show (-(a + b)).toNat = (-a).toNat + (-b).toNat by omega,
          edNatSmul_add _ _ hP, edNeg_edAdd]

theorem edIntSmul_mul (a b : Int) {P : EdPoint} (hP : edOnCurve P = true) :
    edIntSmul (a * b) P = edIntSmul a (edIntSmul b P) := by
  by_cases ha : a ≥ 0
  · obtain ⟨m, rfl⟩ : ∃ m : Nat, a = (m : Int) := ⟨a.toNat, by omega⟩
    by_cases hb : b ≥ 0
    · obtain ⟨n, rfl⟩ : ∃ n : Nat, b = (n : Int) := ⟨b.toNat, by omega⟩
      rw [← Int.natCast_mul, edIntSmul_natCast, edIntSmul_natCast, edIntSmul_natCast,
          edNatSmul_mul _ _ hP]
    · obtain ⟨n, hn⟩ : ∃ n : Nat, b = -(n : Int) := ⟨(-b).toNat, by omega⟩
      rw [hn, Int.mul_neg, edIntSmul_neg _ hP, edIntSmul_neg _ hP,
          edIntSmul_edNeg _ (edOnCurve_edIntSmul _ hP),
          ← Int.natCast_mul, edIntSmul_natCast, edIntSmul_natCast, edIntSmul_natCast,
          edNatSmul_mul _ _ hP]
  · obtain ⟨m, hm⟩ : ∃ m : Nat, a = -(m : Int) := ⟨(-a).toNat, by omega⟩
    rw [hm, Int.neg_mul, edIntSmul_neg _ hP, edIntSmul_neg _ (edOnCurve_edIntSmul _ hP)]
    by_cases hb : b ≥ 0
    · obtain ⟨n, rfl⟩ : ∃ n : Nat, b = (n : Int) := ⟨b.toNat, by omega⟩
      rw [← Int.natCast_mul, edIntSmul_natCast, edIntSmul_natCast, edIntSmul_natCast,
          edNatSmul_mul _ _ hP]
    · obtain ⟨n, hn⟩ : ∃ n : Nat, b = -(n : Int) := ⟨(-b).toNat, by omega⟩
      rw [hn, Int.mul_neg, edIntSmul_neg _ hP, edIntSmul_neg _ hP,
          edIntSmul_edNeg _ (edOnCurve_edIntSmul _ hP),
          ← Int.natCast_mul, edIntSmul_natCast, edIntSmul_natCast, edIntSmul_natCast,
          edNatSmul_mul _ _ hP]

private theorem bv8_signed_radix16_cases :
    ∀ x : BitVec 8, (-8 ≤ x.toInt ∧ x.toInt ≤ 8) →
      (x = 0#8 ∨
       x = 1#8 ∨ x = 2#8 ∨ x = 3#8 ∨ x = 4#8 ∨ x = 5#8 ∨ x = 6#8 ∨ x = 7#8 ∨ x = 8#8 ∨
       x = -1#8 ∨ x = -2#8 ∨ x = -3#8 ∨ x = -4#8 ∨ x = -5#8 ∨ x = -6#8 ∨ x = -7#8 ∨ x = -8#8) := by
  decide

private def selectRaw {α : Type} (f : Nat → α) (zero : α) (x : BitVec 8) : α :=
  if x == 8#8 || x == -8#8 then f 7 else if x == 7#8 || x == -7#8 then f 6
  else if x == 6#8 || x == -6#8 then f 5 else if x == 5#8 || x == -5#8 then f 4
  else if x == 4#8 || x == -4#8 then f 3 else if x == 3#8 || x == -3#8 then f 2
  else if x == 2#8 || x == -2#8 then f 1 else if x == 1#8 || x == -1#8 then f 0
  else zero

private theorem edSelectAffineNiels_eq_selectRaw (slice : List (BitVec 8)) (d : BitVec 8) :
    edSelectAffineNiels slice d =
      let e := selectRaw (edTableEntryAt slice) (1, 1, 0) d
      if d.msb then (e.2.1, e.1, fpNeg e.2.2) else e := by
  change (let (ypx, ymx, xy2d) := selectRaw (edTableEntryAt slice) (1, 1, 0) d
          if d.msb then (ymx, ypx, fpNeg xy2d) else (ypx, ymx, xy2d)) = _
  rcases selectRaw (edTableEntryAt slice) (1, 1, 0) d with ⟨ypx, ymx, xy2d⟩
  rfl

private theorem edSelect_pos_case {slice : List (BitVec 8)} {Q : EdPoint}
    (x : BitVec 8) (j : Nat)
    (hmsb : x.msb = false) (hto : x.toInt = Int.ofNat (j + 1))
    (hraw : ∀ {α : Type} (f : Nat → α) (z : α), selectRaw f z x = f j)
    (hj : let e := edTableEntryAt slice j; EdAffineNielsValid e.1 e.2.1 e.2.2 (edNatSmul (j + 1) Q)) :
    let e := edSelectAffineNiels slice x
    EdAffineNielsValid e.1 e.2.1 e.2.2 (edIntSmul x.toInt Q) := by
  dsimp only
  rw [edSelectAffineNiels_eq_selectRaw]
  dsimp only
  rw [hmsb, hraw, hto, edIntSmul_ofNat]
  simpa only [Bool.false_eq_true, ↓reduceIte] using hj

private theorem edSelect_neg_case {slice : List (BitVec 8)} {Q : EdPoint}
    (x : BitVec 8) (j : Nat)
    (hmsb : x.msb = true) (hneg : ¬(x.toInt ≥ 0)) (habs : (-x.toInt).toNat = j + 1)
    (hraw : ∀ {α : Type} (f : Nat → α) (z : α), selectRaw f z x = f j)
    (hj : let e := edTableEntryAt slice j; EdAffineNielsValid e.1 e.2.1 e.2.2 (edNatSmul (j + 1) Q)) :
    let e := edSelectAffineNiels slice x
    EdAffineNielsValid e.1 e.2.1 e.2.2 (edIntSmul x.toInt Q) := by
  dsimp only
  rw [edSelectAffineNiels_eq_selectRaw]
  dsimp only
  rw [hmsb, hraw]
  have hint : edIntSmul x.toInt Q = edNeg (edNatSmul (j + 1) Q) := by
    unfold edIntSmul; simp only [hneg, ↓reduceIte, habs]
  rw [hint]
  simpa only [↓reduceIte] using edAffineNielsValid_neg hj

private theorem edSelectAffineNiels_valid_proj {slice : List (BitVec 8)} {Q : EdPoint} {d : BitVec 8}
    (htab : ∀ j < 8,
      let (ypx, ymx, xy2d) := edTableEntryAt slice j
      EdAffineNielsValid ypx ymx xy2d (edNatSmul (j + 1) Q))
    (hd : -8 ≤ d.toInt ∧ d.toInt ≤ 8) :
    let e := edSelectAffineNiels slice d
    EdAffineNielsValid e.1 e.2.1 e.2.2 (edIntSmul d.toInt Q) := by
  have htab' : ∀ j < 8,
      let e := edTableEntryAt slice j
      EdAffineNielsValid e.1 e.2.1 e.2.2 (edNatSmul (j + 1) Q) := by
    intro j hj
    have h := htab j hj
    dsimp only
    generalize edTableEntryAt slice j = e at h ⊢
    rcases e with ⟨ypx, ymx, xy2d⟩
    exact h
  have h0 := htab' 0 (by decide)
  have h1 := htab' 1 (by decide)
  have h2 := htab' 2 (by decide)
  have h3 := htab' 3 (by decide)
  have h4 := htab' 4 (by decide)
  have h5 := htab' 5 (by decide)
  have h6 := htab' 6 (by decide)
  have h7 := htab' 7 (by decide)
  rcases bv8_signed_radix16_cases d hd with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · dsimp only
    rw [edSelectAffineNiels_eq_selectRaw]
    dsimp only
    have hraw0 : ∀ {α : Type} (f : Nat → α) (z : α), selectRaw f z 0#8 = z := fun _ _ => rfl
    rw [show (0#8).msb = false by decide, hraw0,
        show (0#8).toInt = 0 by decide, edIntSmul_zero]
    simpa only [Bool.false_eq_true, ↓reduceIte] using edAffineNielsValid_edZero
  · exact edSelect_pos_case 1#8 0 (by decide) (by decide) (fun _ _ => rfl) h0
  · exact edSelect_pos_case 2#8 1 (by decide) (by decide) (fun _ _ => rfl) h1
  · exact edSelect_pos_case 3#8 2 (by decide) (by decide) (fun _ _ => rfl) h2
  · exact edSelect_pos_case 4#8 3 (by decide) (by decide) (fun _ _ => rfl) h3
  · exact edSelect_pos_case 5#8 4 (by decide) (by decide) (fun _ _ => rfl) h4
  · exact edSelect_pos_case 6#8 5 (by decide) (by decide) (fun _ _ => rfl) h5
  · exact edSelect_pos_case 7#8 6 (by decide) (by decide) (fun _ _ => rfl) h6
  · exact edSelect_pos_case 8#8 7 (by decide) (by decide) (fun _ _ => rfl) h7
  · exact edSelect_neg_case (-1#8) 0 (by decide) (by decide) (by decide) (fun _ _ => rfl) h0
  · exact edSelect_neg_case (-2#8) 1 (by decide) (by decide) (by decide) (fun _ _ => rfl) h1
  · exact edSelect_neg_case (-3#8) 2 (by decide) (by decide) (by decide) (fun _ _ => rfl) h2
  · exact edSelect_neg_case (-4#8) 3 (by decide) (by decide) (by decide) (fun _ _ => rfl) h3
  · exact edSelect_neg_case (-5#8) 4 (by decide) (by decide) (by decide) (fun _ _ => rfl) h4
  · exact edSelect_neg_case (-6#8) 5 (by decide) (by decide) (by decide) (fun _ _ => rfl) h5
  · exact edSelect_neg_case (-7#8) 6 (by decide) (by decide) (by decide) (fun _ _ => rfl) h6
  · exact edSelect_neg_case (-8#8) 7 (by decide) (by decide) (by decide) (fun _ _ => rfl) h7

/-! ## 5. Soundness of `checkNielsEntry` & `ed25519BasepointTableBytes` Entries -/

theorem edAffineNielsValid_of_checkNielsEntry {e : Nat × Nat × Nat} {P : EdExtPoint}
    (hP : EdExtValid P) (hchk : checkNielsEntry e P = true) :
    EdAffineNielsValid e.1 e.2.1 e.2.2 (edExtToAffine P) := by
  rcases e with ⟨ypx, ymx, xy2d⟩
  unfold checkNielsEntry at hchk
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hchk
  rcases hchk with ⟨⟨⟨_, hypx⟩, hymx⟩, hxy2d⟩
  have hZ := hP.z_ne_zero
  have hTZ := hP.tz_eq_xy
  have h1 := congrArg Fp.ofNat hypx
  have h2 := congrArg Fp.ofNat hymx
  have h3 := congrArg Fp.ofNat hxy2d
  simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_edD2] at h1 h2 h3
  refine ⟨hP.on_curve, ?_, ?_, ?_⟩
  · rw [edExtToAffine_fp_x, edExtToAffine_fp_y]; grind
  · rw [edExtToAffine_fp_x, edExtToAffine_fp_y]; grind
  · rw [edExtToAffine_fp_x, edExtToAffine_fp_y]; grind

theorem of_checkTable8 {entries : List (Nat × Nat × Nat)} {Bi acc : EdExtPoint} {rem j : Nat}
    (hBi : EdExtValid Bi) (hacc : EdExtValid acc)
    (hchk : checkTable8 entries Bi acc rem = true)
    (hlen : entries.length = rem) (hj : j < rem) :
    let e := entries.getD j (0, 0, 0)
    EdAffineNielsValid e.1 e.2.1 e.2.2
      (edAdd (edExtToAffine acc) (edNatSmul (j + 1) (edExtToAffine Bi))) := by
  induction rem generalizing entries acc j with
  | zero => omega
  | succ rem ih =>
    rcases entries with _ | ⟨e0, rest⟩
    · simp at hlen
    unfold checkTable8 at hchk
    simp only [Bool.and_eq_true] at hchk
    have hacc' : EdExtValid (edExtAdd acc Bi) := edExtValid_edExtAdd hacc hBi
    rcases j with _ | j
    · simp only [List.getD_cons_zero, Nat.zero_add, edNatSmul_one hBi.on_curve,
        ← edExtAdd_toAffine hacc hBi]
      exact edAffineNielsValid_of_checkNielsEntry hacc' hchk.1
    · simp only [List.getD_cons_succ]
      have hsub := @ih rest (edExtAdd acc Bi) j hacc' hchk.2 (by simp at hlen; omega) (by omega)
      rw [edExtAdd_toAffine hacc hBi,
          edAdd_assoc hacc.on_curve hBi.on_curve (edOnCurve_edNatSmul (j + 1) hBi.on_curve),
          ← edNatSmul_succ] at hsub
      exact hsub

theorem of_checkBasepointTable32 {entries : List (Nat × Nat × Nat)} {Bi : EdExtPoint}
    {rem t j : Nat}
    (hBi : EdExtValid Bi)
    (hchk : checkBasepointTable32 entries Bi rem = true)
    (hlen : entries.length = 8 * rem)
    (ht : t < rem) (hj : j < 8) :
    let e := entries.getD (8 * t + j) (0, 0, 0)
    EdAffineNielsValid e.1 e.2.1 e.2.2
      (edNatSmul (j + 1) (edNatSmul (256 ^ t) (edExtToAffine Bi))) := by
  induction rem generalizing entries Bi t with
  | zero => omega
  | succ rem ih =>
    unfold checkBasepointTable32 at hchk
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    rcases hchk with ⟨⟨htake_len, htab8⟩, hrest⟩
    rcases t with _ | t
    · have hget : entries.getD j (0, 0, 0) = (entries.take 8).getD j (0, 0, 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]
      simp only [Nat.mul_zero, Nat.zero_add, Nat.pow_zero, edNatSmul_one hBi.on_curve]
      rw [hget]
      have h0 := of_checkTable8 hBi edExtValid_edExtZero htab8 htake_len hj
      rwa [edExtToAffine_edExtZero, edZero_edAdd (edOnCurve_edNatSmul (j + 1) hBi.on_curve)] at h0
    · obtain ⟨hD4_1_valid, hD4_1_aff⟩ := edDouble4_spec hBi
      obtain ⟨hD4_2_valid, hD4_2_aff⟩ := edDouble4_spec hD4_1_valid
      have hdrop_len : (entries.drop 8).length = 8 * rem := by
        rw [List.length_drop]; omega
      have hget : entries.getD (8 * (t + 1) + j) (0, 0, 0) =
          (entries.drop 8).getD (8 * t + j) (0, 0, 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
            show 8 + (8 * t + j) = 8 * (t + 1) + j by omega]
      rw [hget]
      have hsub := @ih (entries.drop 8) (edDouble4 (edDouble4 Bi)) t hD4_2_valid hrest hdrop_len (by omega)
      rw [hD4_2_aff, hD4_1_aff, ← edNatSmul_mul 16 16 hBi.on_curve,
          show 16 * 16 = 256 by decide,
          ← edNatSmul_mul (256 ^ t) 256 hBi.on_curve,
          ← Nat.pow_succ] at hsub
      exact hsub

theorem ed25519BasepointTable_entry_valid {i j : Nat} (hi : i < 32) (hj : j < 8) :
    let (ypx, ymx, xy2d) := edTableEntryAt
      (ProofLib.ByteSlice.slice ed25519BasepointTableBytes (960 * i) 960) j
    EdAffineNielsValid ypx ymx xy2d
      (edNatSmul (j + 1) (edNatSmul (256 ^ i) edBasepoint)) := by
  have hchk := of_checkBasepointTable32
    (edExtValid_edExtOfAffine edOnCurve_edBasepoint)
    checkBasepointTable32_ed25519
    nielsFromBytes_ed25519BasepointTable_length hi hj
  rw [edExtToAffine_edExtOfAffine edOnCurve_edBasepoint] at hchk
  rw [getD_nielsFromBytes nielsFromBytes_ed25519BasepointTable_length (by omega)] at hchk
  have hentry :
      edTableEntryAt (ProofLib.ByteSlice.slice ed25519BasepointTableBytes (960 * i) 960) j =
      (fe51ValAt ed25519BasepointTableBytes (120 * (8 * i + j)) % p25519,
       fe51ValAt ed25519BasepointTableBytes (120 * (8 * i + j) + 40) % p25519,
       fe51ValAt ed25519BasepointTableBytes (120 * (8 * i + j) + 80) % p25519) := by
    unfold edTableEntryAt
    rw [fe51ValAt_slice_eq _ _ _ _ (by omega),
        fe51ValAt_slice_eq _ _ _ _ (by omega),
        fe51ValAt_slice_eq _ _ _ _ (by omega),
        show 960 * i + 120 * j = 120 * (8 * i + j) by omega,
        show 960 * i + (120 * j + 40) = 120 * (8 * i + j) + 40 by omega,
        show 960 * i + (120 * j + 80) = 120 * (8 * i + j) + 80 by omega]
  rw [hentry]
  exact hchk

/-! ## 6. Signed Radix-16 Recoding (`scalarRadix16Digits`) Value & Digit Bounds -/

/-- Unsigned nibble at index `i` (`0 ≤ i < 64`) of a little-endian byte list `a_bs`. -/
def radix16NibbleAt (a_bs : List (BitVec 8)) (i : Nat) : BitVec 8 :=
  if i % 2 == 0 then a_bs.getD (i / 2) 0#8 &&& 15#8 else a_bs.getD (i / 2) 0#8 >>> 4

/-- Nibbles `[63 - k, ..., 63]` of `a_bs`. -/
def radix16NibblesFrom (a_bs : List (BitVec 8)) : Nat → List (BitVec 8)
  | 0 => []
  | k + 1 => radix16NibbleAt a_bs (63 - k) :: radix16NibblesFrom a_bs k

/-- Recentering pass turning `(d, bs)` into signed radix-16 digits in `[-8, 8]`. -/
def recenterRadix16 (d : Nat) : List (BitVec 8) → List (BitVec 8)
  | [] => [BitVec.ofNat 8 d]
  | b :: bs =>
    BitVec.ofInt 8 (Int.ofNat d - (Int.ofNat d + 8) / 16 * 16) ::
      recenterRadix16 (b.toNat + (d + 8) / 16) bs

/-- Unsigned radix-16 value $d + 16 \sum_j b_j 16^j$ of `(d, bs)`. -/
def nibbleListVal (d : Nat) : List (BitVec 8) → Nat
  | [] => d
  | b :: bs => d + 16 * nibbleListVal b.toNat bs

/-- Signed radix-16 polynomial value $\sum_j d_j 16^j$ of `digits`. -/
def signedRadix16Val : List (BitVec 8) → Int
  | [] => 0
  | x :: xs => x.toInt + 16 * signedRadix16Val xs

/-- All nibbles in `bs` are `< 16`, and if `bs` is non-empty its last nibble is `≤ 7`
    (otherwise `d ≤ 8`). -/
def ValidNibbleTail : Nat → List (BitVec 8) → Prop
  | d, [] => d ≤ 8
  | d, b :: [] => d ≤ 16 ∧ b.toNat ≤ 7
  | d, b :: b2 :: bs => d ≤ 16 ∧ b.toNat < 16 ∧ ValidNibbleTail b.toNat (b2 :: bs)

private theorem radix16NibbleAt_lt (a_bs : List (BitVec 8)) (i : Nat) :
    (radix16NibbleAt a_bs i).toNat < 16 := by
  have h := (by decide : ∀ b : BitVec 8, (b &&& 15#8).toNat < 16 ∧ (b >>> 4).toNat < 16)
    (a_bs.getD (i / 2) 0#8)
  unfold radix16NibbleAt
  split <;> simp only [h.1, h.2]

private theorem radix16NibbleAt_63_le_7 {a_bs : List (BitVec 8)}
    (hb31 : (a_bs.getD 31 0#8).toNat ≤ 127) :
    (radix16NibbleAt a_bs 63).toNat ≤ 7 := by
  unfold radix16NibbleAt
  simp only [show (63 % 2 == 0) = false by decide, Bool.false_eq_true, ↓reduceIte,
    show 63 / 2 = 31 by decide, BitVec.toNat_ushiftRight]
  have : (a_bs.getD 31 0#8).toNat >>> 4 = (a_bs.getD 31 0#8).toNat / 16 :=
    Nat.shiftRight_eq_div_pow _ 4
  omega

private theorem radix16NibbleAt_int_eq (a_bs : List (BitVec 8)) (i : Nat) :
    (if i % 2 == 0 then Int.ofNat ((a_bs.getD (i / 2) 0#8).toNat &&& 0x0f)
     else Int.ofNat ((a_bs.getD (i / 2) 0#8).toNat >>> 4)) =
    Int.ofNat (radix16NibbleAt a_bs i).toNat := by
  unfold radix16NibbleAt
  split <;> simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]

private theorem scalarRadix16Digits_go_eq_recenter (a_bs : List (BitVec 8)) :
    ∀ (k : Nat) (_hk : k ≤ 63) (carry : Nat) (acc : List (BitVec 8)),
      scalarRadix16Digits.go a_bs (k + 1) (Int.ofNat carry) acc =
        acc.reverse ++ recenterRadix16 ((radix16NibbleAt a_bs (63 - k)).toNat + carry)
          (radix16NibblesFrom a_bs k) := by
  intro k
  induction k with
  | zero =>
    intro _ carry acc
    rw [scalarRadix16Digits.go, radix16NibbleAt_int_eq]
    change scalarRadix16Digits.go a_bs 0 0
      (BitVec.ofNat 8 ((radix16NibbleAt a_bs 63).toNat + carry) :: acc) = _
    rw [scalarRadix16Digits.go]
    simp [radix16NibblesFrom, recenterRadix16]
  | succ m ih =>
    intro hk carry acc
    rw [scalarRadix16Digits.go, radix16NibbleAt_int_eq]
    have hm : 63 - (m + 1) < 63 := by omega
    let dNat := (radix16NibbleAt a_bs (63 - (m + 1))).toNat + carry
    change (if 63 - (m + 1) < 63 then
        scalarRadix16Digits.go a_bs (m + 1) (Int.ofNat ((dNat + 8) / 16))
          (BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16) :: acc)
      else
        scalarRadix16Digits.go a_bs (m + 1) 0 (BitVec.ofInt 8 (Int.ofNat dNat) :: acc)) = _
    simp only [hm, ↓reduceIte]
    rw [ih (by omega) ((dNat + 8) / 16)]
    simp [radix16NibblesFrom, recenterRadix16, dNat]

theorem scalarRadix16Digits_eq_recenter (a_bs : List (BitVec 8)) :
    scalarRadix16Digits a_bs =
      recenterRadix16 (radix16NibbleAt a_bs 0).toNat (radix16NibblesFrom a_bs 63) := by
  unfold scalarRadix16Digits
  simpa using scalarRadix16Digits_go_eq_recenter a_bs 63 (by omega) 0 []

private theorem ofInt8_recenter_props {d : Nat} (hd : d ≤ 16) :
    let r : Int := Int.ofNat d - (Int.ofNat d + 8) / 16 * 16
    (BitVec.ofInt 8 r).toInt = r ∧ -8 ≤ r ∧ r ≤ 8 ∧ (d + 8) / 16 ≤ 1 ∧
    r + 16 * Int.ofNat ((d + 8) / 16) = Int.ofNat d := by
  have hfin : ∀ k : Fin 17,
      let d := k.val
      let r : Int := Int.ofNat d - (Int.ofNat d + 8) / 16 * 16
      (BitVec.ofInt 8 r).toInt = r ∧ -8 ≤ r ∧ r ≤ 8 ∧ (d + 8) / 16 ≤ 1 ∧
      r + 16 * Int.ofNat ((d + 8) / 16) = Int.ofNat d := by decide
  exact hfin ⟨d, by omega⟩

private theorem ofNat8_le8_props {d : Nat} (hd : d ≤ 8) :
    (BitVec.ofNat 8 d).toInt = Int.ofNat d ∧
    -8 ≤ (BitVec.ofNat 8 d).toInt ∧ (BitVec.ofNat 8 d).toInt ≤ 8 := by
  have hfin : ∀ k : Fin 9,
      (BitVec.ofNat 8 k.val).toInt = Int.ofNat k.val ∧
      -8 ≤ (BitVec.ofNat 8 k.val).toInt ∧ (BitVec.ofNat 8 k.val).toInt ≤ 8 := by decide
  exact hfin ⟨d, by omega⟩

theorem recenterRadix16_spec (d : Nat) (bs : List (BitVec 8))
    (hv : ValidNibbleTail d bs) :
    (∀ x ∈ recenterRadix16 d bs, -8 ≤ x.toInt ∧ x.toInt ≤ 8) ∧
    signedRadix16Val (recenterRadix16 d bs) = Int.ofNat (nibbleListVal d bs) := by
  induction bs generalizing d with
  | nil =>
    have hd : d ≤ 8 := hv
    obtain ⟨hto, hlo, hhi⟩ := ofNat8_le8_props hd
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [recenterRadix16, List.mem_singleton] at hx
      subst hx
      exact ⟨hlo, hhi⟩
    · simp only [recenterRadix16, signedRadix16Val, nibbleListVal, hto, Int.mul_zero, Int.add_zero]
  | cons b rest ih =>
    have hv' : d ≤ 16 ∧ ValidNibbleTail (b.toNat + (d + 8) / 16) rest := by
      rcases rest with _ | ⟨b2, rest'⟩
      · rcases hv with ⟨hd, hb⟩
        have hc : (d + 8) / 16 ≤ 1 := by omega
        exact ⟨hd, by unfold ValidNibbleTail; omega⟩
      · rcases hv with ⟨hd, hb, htail⟩
        have hc : (d + 8) / 16 ≤ 1 := by omega
        rcases rest' with _ | ⟨b3, rest''⟩
        · exact ⟨hd, by omega, htail.2⟩
        · exact ⟨hd, by omega, htail.2.1, htail.2.2⟩
    obtain ⟨hto, hlo, hhi, _, heq_d⟩ := ofInt8_recenter_props hv'.1
    obtain ⟨hmem_ih, hval_ih⟩ := ih (b.toNat + (d + 8) / 16) hv'.2
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [recenterRadix16, List.mem_cons] at hx
      rcases hx with rfl | hx_tl
      · rw [hto]; exact ⟨hlo, hhi⟩
      · exact hmem_ih x hx_tl
    · simp only [recenterRadix16, signedRadix16Val, nibbleListVal, hto, hval_ih]
      rcases rest with _ | ⟨b2, rest'⟩ <;>
        simp only [nibbleListVal, Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul] at heq_d ⊢ <;>
        omega

private theorem validNibbleTail_nibblesFrom {a_bs : List (BitVec 8)}
    (hb31 : (a_bs.getD 31 0#8).toNat ≤ 127) :
    ∀ (k : Nat) (_hk : 1 ≤ k) (_hle : k ≤ 63) (d : Nat) (_hd : d ≤ 16),
      ValidNibbleTail d (radix16NibblesFrom a_bs k) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ m ih =>
    intro _ hle d hd
    rcases m with _ | m'
    · exact ⟨hd, radix16NibbleAt_63_le_7 hb31⟩
    · simp only [radix16NibblesFrom]
      exact ⟨hd, radix16NibbleAt_lt a_bs _, ih (by omega) (by omega) _ (Nat.le_of_lt (radix16NibbleAt_lt a_bs _))⟩

private theorem byte_split_nibbles (b : BitVec 8) :
    (b &&& 15#8).toNat + 16 * (b >>> 4).toNat = b.toNat := by
  revert b; decide

private theorem nibblePair_val (a_bs : List (BitVec 8)) :
    ∀ k : Nat, k ≤ 31 →
      nibbleListVal (radix16NibbleAt a_bs (62 - 2 * k)).toNat
        (radix16NibblesFrom a_bs (2 * k + 1)) =
      (List.range (k + 1)).foldr (fun idx acc => acc * 256 + (a_bs.getD (31 - k + idx) 0#8).toNat) 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Nat.mul_zero, Nat.sub_zero, Nat.zero_add, Nat.add_zero, Nat.zero_mul,
      radix16NibblesFrom, nibbleListVal, List.range_one, List.foldr_cons, List.foldr_nil]
    unfold radix16NibbleAt
    simp only [show (62 % 2 == 0) = true by decide, show (63 % 2 == 0) = false by decide,
      Bool.false_eq_true, ↓reduceIte, show 62 / 2 = 31 by decide]
    exact byte_split_nibbles (a_bs.getD 31 0#8)
  | succ m ih =>
    intro hm
    have hstep : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
    rw [hstep, radix16NibblesFrom, radix16NibblesFrom, nibbleListVal, nibbleListVal]
    have hi2 : 63 - (2 * m + 1) = 62 - 2 * m := by omega
    rw [hi2, ih (by omega)]
    have heven : ((62 - 2 * (m + 1)) % 2 == 0) = true := by simp only [beq_iff_eq]; omega
    have hodd : ¬((63 - ((2 * m + 1) + 1)) % 2 == 0) := by simp only [beq_iff_eq]; omega
    have hdiv1 : (62 - 2 * (m + 1)) / 2 = 31 - (m + 1) := by omega
    have hdiv2 : (63 - ((2 * m + 1) + 1)) / 2 = 31 - (m + 1) := by omega
    have hlo : (radix16NibbleAt a_bs (62 - 2 * (m + 1))).toNat =
        (a_bs.getD (31 - (m + 1)) 0#8 &&& 15#8).toNat := by
      unfold radix16NibbleAt; simp only [heven, ↓reduceIte, hdiv1]
    have hhi : (radix16NibbleAt a_bs (63 - ((2 * m + 1) + 1))).toNat =
        (a_bs.getD (31 - (m + 1)) 0#8 >>> 4).toNat := by
      unfold radix16NibbleAt; simp only [hodd, hdiv2]; rfl
    rw [hlo, hhi]
    have hpair := byte_split_nibbles (a_bs.getD (31 - (m + 1)) 0#8)
    have hrange : List.range (m + 1 + 1) = 0 :: (List.range (m + 1)).map Nat.succ :=
      List.range_succ_eq_map
    rw [hrange, List.foldr_cons, List.foldr_map]
    simp only [Nat.add_zero]
    have hshift :
        (List.range (m + 1)).foldr (fun x acc => acc * 256 + (a_bs.getD (31 - (m + 1) + x.succ) 0#8).toNat) 0 =
        (List.range (m + 1)).foldr (fun idx acc => acc * 256 + (a_bs.getD (31 - m + idx) 0#8).toNat) 0 := by
      congr 1; funext idx acc; rw [show 31 - (m + 1) + idx.succ = 31 - m + idx by omega]
    rw [hshift]
    omega

private theorem foldr_range_getD_eq_leBytesToNat :
    ∀ (bs : List (BitVec 8)) (n : Nat), bs.length = n →
      (List.range n).foldr (fun idx acc => acc * 256 + (bs.getD idx 0#8).toNat) 0 =
        leBytesToNat bs := by
  intro bs
  induction bs with
  | nil =>
    intro n hn; subst hn; rfl
  | cons b rest ih =>
    intro n hn; subst hn
    simp only [List.length_cons, List.range_succ_eq_map, List.foldr_cons, List.foldr_map,
      List.getD_cons_zero, List.getD_cons_succ, leBytesToNat_cons]
    rw [ih rest.length rfl]

theorem scalarRadix16Digits_spec {scalar_bs : List (BitVec 8)}
    (hlen : scalar_bs.length = 32)
    (hb31 : (scalar_bs.getD 31 0#8).toNat ≤ 127) :
    (∀ k < 64,
      let d := (scalarRadix16Digits scalar_bs).getD k 0#8;
      -8 ≤ d.toInt ∧ d.toInt ≤ 8) ∧
    signedRadix16Val (scalarRadix16Digits scalar_bs) = Int.ofNat (leBytesToNat scalar_bs) := by
  have hv : ValidNibbleTail (radix16NibbleAt scalar_bs 0).toNat (radix16NibblesFrom scalar_bs 63) :=
    validNibbleTail_nibblesFrom hb31 63 (by decide) (by decide) _
      (Nat.le_of_lt (radix16NibbleAt_lt scalar_bs 0))
  obtain ⟨hmem, hval⟩ := recenterRadix16_spec _ _ hv
  rw [← scalarRadix16Digits_eq_recenter] at hmem hval
  have hlen64 : (scalarRadix16Digits scalar_bs).length = 64 := scalarRadix16Digits_length scalar_bs
  refine ⟨?_, ?_⟩
  · intro k hk
    have hk_lt : k < (scalarRadix16Digits scalar_bs).length := by omega
    have hget : (scalarRadix16Digits scalar_bs).getD k 0#8 = (scalarRadix16Digits scalar_bs)[k]'hk_lt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt]; rfl
    rw [hget]
    exact hmem _ (List.getElem_mem hk_lt)
  · rw [hval]
    have hp := nibblePair_val scalar_bs 31 (by decide)
    simp only [show 62 - 2 * 31 = 0 by decide, show 2 * 31 + 1 = 63 by decide,
      show 31 + 1 = 32 by decide, Nat.zero_add] at hp
    rw [hp, foldr_range_getD_eq_leBytesToNat scalar_bs 32 hlen]

/-! ## 7. `edMulBase` Equivalence to `edSmul` & Point Compression Corollary -/

/-- Weighted digit sum $\sum_{r=0}^{\text{rem}-1} d_{2(i+r)+\text{parity}} \cdot 256^{i+r}$. -/
def radix256DigitSum (digits : List (BitVec 8)) (parity : Nat) : Nat → Nat → Int
  | _, 0 => 0
  | i, rem + 1 =>
    (digits.getD (2 * i + parity) 0#8).toInt * (256 : Int) ^ i +
      radix256DigitSum digits parity (i + 1) rem

private theorem edMulBaseStepAt_eq (table_bs digits : List (BitVec 8)) (parity i : Nat) (acc : EdExtPoint) :
    edMulBaseStepAt table_bs digits parity i acc =
      let sel := edSelectAffineNiels (ProofLib.ByteSlice.slice table_bs (960 * i) 960)
        (digits.getD (2 * i + parity) 0#8)
      edAsExtended (edAddAffineNiels acc sel.1 sel.2.1 sel.2.2) := by
  unfold edMulBaseStepAt edMulBaseStep
  rcases edSelectAffineNiels (ProofLib.ByteSlice.slice table_bs (960 * i) 960)
    (digits.getD (2 * i + parity) 0#8) with ⟨ypx, ymx, xy2d⟩
  rfl
attribute [local irreducible] edAdd edSub edBasepoint edSmul encodeEd
  edExtToAffine edCompToAffine edSelectAffineNiels edAddAffineNiels edAsExtended edDouble4

private theorem int_pow_256_eq_ofNat (i : Nat) :
    ((256 : Int) ^ i) = Int.ofNat (256 ^ i) := by
  rw [Int.ofNat_eq_natCast, Int.natCast_pow]; rfl

private theorem edMulBaseStepAt_spec (table_bs digits : List (BitVec 8)) (parity i : Nat)
    (acc : EdExtPoint) {Q : EdPoint} (hQ : edOnCurve Q = true)
    (htab : ∀ j < 8,
      let (ypx, ymx, xy2d) := edTableEntryAt
        (ProofLib.ByteSlice.slice table_bs (960 * i) 960) j
      EdAffineNielsValid ypx ymx xy2d
        (edNatSmul (j + 1) (edNatSmul (256 ^ i) Q)))
    (hd : -8 ≤ (digits.getD (2 * i + parity) 0#8).toInt ∧
          (digits.getD (2 * i + parity) 0#8).toInt ≤ 8)
    (hacc : EdExtValid acc) :
    EdExtValid (edMulBaseStepAt table_bs digits parity i acc) ∧
    edExtToAffine (edMulBaseStepAt table_bs digits parity i acc) =
      edAdd (edExtToAffine acc)
        (edIntSmul ((digits.getD (2 * i + parity) 0#8).toInt * (256 : Int) ^ i) Q) := by
  have hsel := edSelectAffineNiels_valid_proj htab hd
  rw [edMulBaseStepAt_eq]
  dsimp only
  generalize edSelectAffineNiels (ProofLib.ByteSlice.slice table_bs (960 * i) 960)
    (digits.getD (2 * i + parity) 0#8) = sel at hsel ⊢
  have hcomp_valid : EdCompValid (edAddAffineNiels acc sel.1 sel.2.1 sel.2.2) :=
    edCompValid_edAddAffineNiels hacc hsel
  refine ⟨edExtValid_edAsExtended hcomp_valid, ?_⟩
  rw [edAsExtended_toAffine hcomp_valid, edAddAffineNiels_toAffine hacc hsel,
      edIntSmul_mul _ ((256 : Int) ^ i) hQ,
      int_pow_256_eq_ofNat i, edIntSmul_ofNat]

private theorem edMulBase_aff_step {P Q : EdPoint} (a b : Int)
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    edAdd (edAdd P (edIntSmul a Q)) (edIntSmul b Q) =
      edAdd P (edIntSmul (a + b) Q) := by
  rw [edIntSmul_add a b hQ,
      edAdd_assoc hP (edOnCurve_edIntSmul a hQ)
        (edOnCurve_edIntSmul b hQ)]

private theorem edMulBaseLoopWith_zero_fast {α : Type} (step : Nat → α → α) (i : Nat) (acc : α) :
    edMulBaseLoopWith step i 0 acc = acc := rfl

private theorem edMulBaseLoopWith_step_fast {α : Type} (step : Nat → α → α) (i rem : Nat) (acc : α) :
    edMulBaseLoopWith step i (rem + 1) acc = edMulBaseLoopWith step (i + 1) rem (step i acc) := rfl

private theorem edMulBaseLoop_zero_fast (table_bs digits : List (BitVec 8)) (parity i : Nat) (acc : EdExtPoint) :
    edMulBaseLoop table_bs digits parity i 0 acc = acc :=
  edMulBaseLoopWith_zero_fast (edMulBaseStepAt table_bs digits parity) i acc

private theorem edMulBaseLoop_step_fast (table_bs digits : List (BitVec 8)) (parity i rem : Nat) (acc : EdExtPoint) :
    edMulBaseLoop table_bs digits parity i (rem + 1) acc =
      edMulBaseLoop table_bs digits parity (i + 1) rem (edMulBaseStepAt table_bs digits parity i acc) :=
  edMulBaseLoopWith_step_fast (edMulBaseStepAt table_bs digits parity) i rem acc

attribute [local irreducible] edMulBaseLoop edMulBaseStepAt

private theorem edMulBaseLoop_spec_gen (table_bs : List (BitVec 8))
    {Q : EdPoint} (hQ : edOnCurve Q = true)
    (htable : ∀ i < 32, ∀ j < 8,
      let (ypx, ymx, xy2d) := edTableEntryAt
        (ProofLib.ByteSlice.slice table_bs (960 * i) 960) j
      EdAffineNielsValid ypx ymx xy2d
        (edNatSmul (j + 1) (edNatSmul (256 ^ i) Q)))
    {digits : List (BitVec 8)} (parity : Nat)
    (hdigits : ∀ k < 64, -8 ≤ (digits.getD k 0#8).toInt ∧ (digits.getD k 0#8).toInt ≤ 8)
    (hparity : parity ≤ 1) :
    ∀ (rem i : Nat) (acc : EdExtPoint),
      i + rem ≤ 32 →
      EdExtValid acc →
      EdExtValid (edMulBaseLoop table_bs digits parity i rem acc) ∧
      edExtToAffine (edMulBaseLoop table_bs digits parity i rem acc) =
        edAdd (edExtToAffine acc)
          (edIntSmul (radix256DigitSum digits parity i rem) Q)
  | 0, i, acc, _, hacc => by
    rw [edMulBaseLoop_zero_fast, radix256DigitSum, edIntSmul_zero, edAdd_edZero hacc.on_curve]
    exact ⟨hacc, rfl⟩
  | rem + 1, i, acc, hrem, hacc => by
    have hi : i < 32 := by omega
    have hk : 2 * i + parity < 64 := by omega
    obtain ⟨hacc'_valid, hacc'_aff⟩ := edMulBaseStepAt_spec table_bs digits parity i acc hQ
      (fun j hj => htable i hi j hj) (hdigits (2 * i + parity) hk) hacc
    obtain ⟨hres_valid, hres_aff⟩ :=
      edMulBaseLoop_spec_gen table_bs hQ htable parity hdigits hparity
        rem (i + 1) (edMulBaseStepAt table_bs digits parity i acc) (by omega) hacc'_valid
    rw [edMulBaseLoop_step_fast]
    refine ⟨hres_valid, ?_⟩
    rw [hres_aff, hacc'_aff, radix256DigitSum]
    exact edMulBase_aff_step _ _ hacc.on_curve hQ

private theorem list_drop_two_eq {α : Type} :
    ∀ (xs : List α) (n : Nat) (hn0 : n < xs.length) (hn1 : n + 1 < xs.length),
      xs.drop n = (xs[n]'hn0) :: (xs[n + 1]'hn1) :: xs.drop (n + 2)
  | _ :: _ :: _, 0, _, _ => rfl
  | _ :: xs, n + 1, hn0, hn1 =>
    list_drop_two_eq xs n (by simp at hn0; omega) (by simp at hn1; omega)
  | [], _, hn0, _ => by simp at hn0
  | [_], 0, _, hn1 => by simp at hn1

private theorem signedRadix16Val_drop_pair (digits : List (BitVec 8)) (hlen : digits.length = 64) :
    ∀ rem : Nat, rem ≤ 32 →
      let i := 32 - rem
      16 * radix256DigitSum digits 1 i rem + radix256DigitSum digits 0 i rem =
        (256 : Int) ^ i * signedRadix16Val (digits.drop (2 * i)) := by
  intro rem
  induction rem with
  | zero =>
    intro _
    have hdrop : digits.drop 64 = [] := List.drop_of_length_le (by omega)
    simp [radix256DigitSum, hdrop, signedRadix16Val]
  | succ r ih =>
    intro hr
    have ih_r := ih (by omega)
    dsimp only at ih_r
    let i := 32 - (r + 1)
    have hi_succ : 32 - r = i + 1 := by omega
    change 16 * radix256DigitSum digits 1 i (r + 1) + radix256DigitSum digits 0 i (r + 1) =
      (256 : Int) ^ i * signedRadix16Val (digits.drop (2 * i))
    rw [radix256DigitSum, radix256DigitSum, ← hi_succ]
    have h2i_lt : 2 * i < digits.length := by omega
    have h2i1_lt : 2 * i + 1 < digits.length := by omega
    have hdrop_step :
        digits.drop (2 * i) =
        (digits[2 * i]'h2i_lt) :: (digits[2 * i + 1]'h2i1_lt) :: digits.drop (2 * (32 - r)) := by
      rw [list_drop_two_eq digits (2 * i) h2i_lt h2i1_lt,
          show 2 * i + 2 = 2 * (32 - r) by omega]
    have hd0 : digits.getD (2 * i + 0) 0#8 = digits[2 * i]'h2i_lt := by
      rw [Nat.add_zero, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2i_lt]; rfl
    have hd1 : digits.getD (2 * i + 1) 0#8 = digits[2 * i + 1]'h2i1_lt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2i1_lt]; rfl
    rw [hdrop_step, signedRadix16Val, signedRadix16Val, hd0, hd1]
    have hpow : (256 : Int) ^ (32 - r) = (256 : Int) ^ i * 256 := by
      rw [hi_succ, Int.pow_succ]
    rw [hpow] at ih_r
    grind

/-- Parametric basepoint-table scalar multiplication soundness (`edMulBase_spec_gen`):
    for any valid curve point `Q` whose 32-subtable `EdwardsBasepointTable` `table_bs` holds
    `[j + 1]([256^i]Q)` at entry `(i, j)`, `edMulBase table_bs scalar_bs` produces a valid
    extended point with affine projection `edSmul (leBytesToNat scalar_bs) Q`. -/
theorem edMulBase_spec_gen (table_bs : List (BitVec 8))
    {Q : EdPoint} (hQ : edOnCurve Q = true)
    (htable : ∀ i < 32, ∀ j < 8,
      let (ypx, ymx, xy2d) := edTableEntryAt
        (ProofLib.ByteSlice.slice table_bs (960 * i) 960) j
      EdAffineNielsValid ypx ymx xy2d
        (edNatSmul (j + 1) (edNatSmul (256 ^ i) Q)))
    {scalar_bs : List (BitVec 8)}
    (hlen : scalar_bs.length = 32)
    (hb31 : (scalar_bs.getD 31 0#8).toNat ≤ 127) :
    EdExtValid (edMulBase table_bs scalar_bs) ∧
    edExtToAffine (edMulBase table_bs scalar_bs) =
      edSmul (leBytesToNat scalar_bs) Q := by
  dsimp only [edMulBase]
  let digits := scalarRadix16Digits scalar_bs
  obtain ⟨hdigits, hval⟩ := scalarRadix16Digits_spec hlen hb31
  obtain ⟨hodd_valid, hodd_aff⟩ :=
    edMulBaseLoop_spec_gen table_bs hQ htable 1 hdigits (by decide) 32 0 edExtZero (by decide) edExtValid_edExtZero
  rw [edExtToAffine_edExtZero, edZero_edAdd (edOnCurve_edIntSmul _ hQ)] at hodd_aff
  obtain ⟨hd4_valid, hd4_aff⟩ := edDouble4_spec hodd_valid
  obtain ⟨heven_valid, heven_aff⟩ :=
    edMulBaseLoop_spec_gen table_bs hQ htable 0 hdigits (by decide) 32 0
      (edDouble4 (edMulBaseLoop table_bs digits 1 0 32 edExtZero))
      (by decide) hd4_valid
  refine ⟨heven_valid, ?_⟩
  have hd4_int :
      edExtToAffine (edDouble4 (edMulBaseLoop table_bs digits 1 0 32 edExtZero)) =
      edIntSmul (16 * radix256DigitSum digits 1 0 32) Q := by
    rw [hd4_aff, hodd_aff, ← edIntSmul_ofNat 16,
        ← edIntSmul_mul (Int.ofNat 16) _ hQ]
    rfl
  rw [heven_aff, hd4_int, ← edIntSmul_add _ _ hQ]
  have hsum := signedRadix16Val_drop_pair digits (scalarRadix16Digits_length scalar_bs) 32 (by decide)
  simp only [Nat.sub_self, Nat.mul_zero, List.drop_zero, Int.pow_zero, Int.one_mul] at hsum
  have hlt : leBytesToNat scalar_bs < 2 ^ 256 := by
    have h1 := leBytesToNat_lt scalar_bs
    rwa [hlen, show 256 ^ 32 = 2 ^ 256 by decide] at h1
  rw [hsum, hval, edIntSmul_ofNat, ← edSmul_eq_edNatSmul hlt hQ]

/-- **Main Basepoint Scalar Multiplication Bridge (`edMulBase_spec`)**:
    for any 32-byte scalar `scalar_bs` with `scalar_bs[31] ≤ 127`, `edMulBase` produces a valid
    extended point whose affine projection equals `edSmul (leBytesToNat scalar_bs) edBasepoint`. -/
theorem edMulBase_spec {scalar_bs : List (BitVec 8)}
    (hlen : scalar_bs.length = 32)
    (hb31 : (scalar_bs.getD 31 0#8).toNat ≤ 127) :
    EdExtValid (edMulBase ed25519BasepointTableBytes scalar_bs) ∧
    edExtToAffine (edMulBase ed25519BasepointTableBytes scalar_bs) =
      edSmul (leBytesToNat scalar_bs) edBasepoint :=
  edMulBase_spec_gen ed25519BasepointTableBytes edOnCurve_edBasepoint
    (fun _ hi _ hj => ed25519BasepointTable_entry_valid hi hj) hlen hb31


theorem clampScalarBytes_length_of_eq32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    (clampScalarBytes bs).length = 32 := by
  unfold clampScalarBytes
  simp only [List.length_append, List.length_singleton, List.length_take, List.length_drop, h]
  omega

private theorem b31_clamped_le_127_aux : ∀ b31 : BitVec 8, ((b31 &&& 0x7f#8) ||| 0x40#8).toNat ≤ 127 := by decide

theorem clampScalarBytes_getD31_le_127 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ((clampScalarBytes bs).getD 31 0#8).toNat ≤ 127 := by
  unfold clampScalarBytes
  have hd : ((bs.drop 1).take 30).length = 30 := by simp [h]
  rw [List.append_assoc, List.singleton_append, List.getD_cons_succ,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp only [hd, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  exact b31_clamped_le_127_aux _

theorem leBytesToNat_clampScalarBytes_eq_clampScalar {bs : List (BitVec 8)} (h : bs.length = 32) :
    leBytesToNat (clampScalarBytes bs) = clampScalar bs := by
  unfold clampScalar
  rw [List.take_of_length_le (by omega)]

theorem edMulBase_clampScalarBytes_spec {bs : List (BitVec 8)} (hlen : bs.length = 32) :
    EdExtValid (edMulBase ed25519BasepointTableBytes (clampScalarBytes bs)) ∧
    edExtToAffine (edMulBase ed25519BasepointTableBytes (clampScalarBytes bs)) =
      edSmul (clampScalar bs) edBasepoint := by
  have ⟨hv, ha⟩ := edMulBase_spec (clampScalarBytes_length_of_eq32 hlen) (clampScalarBytes_getD31_le_127 hlen)
  rw [leBytesToNat_clampScalarBytes_eq_clampScalar hlen] at ha
  exact ⟨hv, ha⟩

theorem edMulBase_clampScalarBytes_valid {bs : List (BitVec 8)} (hlen : bs.length = 32) :
    EdExtValid (edMulBase ed25519BasepointTableBytes (clampScalarBytes bs)) :=
  (edMulBase_clampScalarBytes_spec hlen).1

theorem edMulBase_clampScalarBytes_toAffine {bs : List (BitVec 8)} (hlen : bs.length = 32) :
    edExtToAffine (edMulBase ed25519BasepointTableBytes (clampScalarBytes bs)) =
      edSmul (clampScalar bs) edBasepoint :=
  (edMulBase_clampScalarBytes_spec hlen).2

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.ScalarMul2

end
end

section
section
set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PubFromSecretMath

open X25519Dalek
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational

/-- Projective `(Z + Y) * (Z - Y)⁻¹ mod p` agrees with affine `edToMontU (edExtToAffine P)`
    for every valid extended twisted Edwards point `P`. -/
theorem edExtToMontgomeryU_eq_edToMontU_of_valid {P : EdExtPoint} (hP : EdExtValid P) :
    edExtToMontgomeryU P = X25519Dalek.edToMontU (edExtToAffine P) :=
  (edToMontU_edExtToAffine ((Fp.ofNat_ne_zero_iff P.Z).mp hP.z_ne_zero)).symm

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PubFromSecretMath

theorem X25519Dalek.edExtToMontgomeryU_mulBase_clamped_dev (s : List (BitVec 8)) (hs : s.length = 32) : X25519Dalek.natToLeBytes 32 (X25519Dalek.edExtToMontgomeryU (X25519Dalek.edMulBase X25519Dalek.ed25519BasepointTableBytes (X25519Dalek.clampScalarBytes s))) = X25519Dalek.x25519Pubkey s := by
  rw [LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PubFromSecretMath.edExtToMontgomeryU_eq_edToMontU_of_valid
      (LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.ScalarMul2.edMulBase_clampScalarBytes_valid hs),
    LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.ScalarMul2.edMulBase_clampScalarBytes_toAffine hs,
    X25519Dalek.x25519Pubkey_eq_edToMontU s]

end
end

section
open X25519Dalek

theorem solution (s : List (BitVec 8)) (hs : s.length = 32) :
    natToLeBytes 32
        (edExtToMontgomeryU (edMulBase ed25519BasepointTableBytes (clampScalarBytes s))) =
      x25519Pubkey s := by
  apply X25519Dalek.edExtToMontgomeryU_mulBase_clamped_dev <;> assumption

end
