-- Prove2me | solution 1 for RuntimeTransfer.packing_parameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T11:26:18.717815+00:00
-- url     : https://prove2.me/submissions/732d1229-b4ca-48a6-87bb-64ee2b323c48

import Definitions.Def_RuntimeTransferPacking
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_IntMul_HvdH_kronMul_eq

set_option autoImplicit false
namespace RuntimeTransfer

theorem packing_oracle_transfer (p r : ℕ) (a b : List ℤ)
    (ha : a.length = r) (hb : b.length = r)
    (hab : ∀ x ∈ a, |x| ≤ 2 ^ p) (hbb : ∀ x ∈ b, |x| ≤ 2 ^ p)
    (hr : 1 ≤ r) (hrp : 2 * r < 2 ^ p)
    (oracle : (ℤ × ℤ) → ℤ × ℕ) (T : (ℤ × ℤ) → ℕ) (E D : ℕ)
    (hcorrect : ∀ q, (oracle q).1 = q.1 * q.2)
    (hcost : ∀ q, (oracle q).2 ≤ T q) :
    ((packingProgram p r a b E D).run oracle).1 = IntMul.HvdH.polyMul a b ∧
      ((packingProgram p r a b E D).run oracle).2 ≤ E + D + T (packedQuery p a b) := by
  simp only [packingProgram, Program.run, hcorrect]
  constructor
  · exact IntMul.HvdH.kronMul_eq p r a b ha hb hab hbb hr hrp
  · simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using Nat.add_le_add_left (Nat.add_le_add_right (hcost (packedQuery p a b)) D) E

end RuntimeTransfer


set_option autoImplicit false
namespace RuntimeTransfer

theorem pack_abs_bound (B : ℤ) (hB : 1 ≤ B) (a : List ℤ)
    (ha : ∀ x ∈ a, |x| ≤ B - 1) :
    |IntMul.HvdH.kpack B a| ≤ B ^ a.length - 1 := by
  induction a with
  | nil => simp [IntMul.HvdH.kpack]
  | cons c cs ih =>
    have hc := ha c (by simp)
    have ht := ih (fun x hx => ha x (by simp [hx]))
    calc
      |IntMul.HvdH.kpack B (c :: cs)| ≤ |c| + |B * IntMul.HvdH.kpack B cs| :=
        abs_add_le _ _
      _ = |c| + B * |IntMul.HvdH.kpack B cs| := by
        rw [abs_mul, abs_of_nonneg (by omega : 0 ≤ B)]
      _ ≤ (B - 1) + B * (B ^ cs.length - 1) :=
        add_le_add hc (mul_le_mul_of_nonneg_left ht (by omega))
      _ = B ^ (c :: cs).length - 1 := by simp only [List.length_cons, pow_succ]; ring

theorem packed_operand_bits (p : ℕ) (hp : 1 ≤ p) (a : List ℤ)
    (ha : ∀ x ∈ a, |x| ≤ 2 ^ p) :
    (IntMul.HvdH.kpack (2 ^ (3 * p)) a).natAbs.size ≤ 3 * p * a.length := by
  have hpow : (2 : ℤ) ^ p < 2 ^ (3 * p) := by
    apply pow_lt_pow_right₀ (by norm_num)
    omega
  have hb := pack_abs_bound ((2 : ℤ) ^ (3 * p)) (by
    have := pow_pos (by norm_num : (0 : ℤ) < 2) (3 * p)
    omega) a
    (fun x hx => (ha x hx).trans (by omega))
  have hh : |IntMul.HvdH.kpack (2 ^ (3 * p)) a| < (2 : ℤ) ^ (3 * p * a.length) := by
    rw [pow_mul (2 : ℤ) (3 * p) a.length]
    omega
  apply Nat.size_le.mpr
  rw [← Int.natCast_natAbs] at hh
  exact_mod_cast hh

end RuntimeTransfer
open RuntimeTransfer
theorem solution (b r : ℕ) (hr : 1 ≤ r) :
    b ≤ b + (2 * r).size ∧ 1 ≤ b + (2 * r).size ∧
      2 * r < 2 ^ (b + (2 * r).size) := by
  have hs : 0 < (2 * r).size := Nat.size_pos.mpr (by omega)
  refine ⟨by omega, by omega, ?_⟩
  exact (Nat.lt_size_self (2 * r)).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
#print axioms solution
