-- Prove2me | solution 1 for P2M_FixedOrderFactor_correctionFactor_eq_mul__b1856a05bcec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:55.583365+00:00
-- url     : https://prove2.me/submissions/be6abdff-16f3-4e40-88cf-adfa2ef41814

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order
public import Theorems.Thm_FixedOrderFactor_inv_q_pos
public import Theorems.Thm_FixedOrderFactor_pow_inv_q_lt_one
public import Theorems.Thm_FixedOrderFactor_zetaN_eq
public import Theorems.Thm_FixedOrderFactor_zetaN_pos


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    correctionFactor N r =
      correctionFactor ∅ r * ∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ r) / (1 + (1 / (q : ℝ)) ^ r) := by
  have hterm : ∀ q ∈ N, (1 - (1 / (q : ℝ)) ^ r) / (1 + (1 / (q : ℝ)) ^ r) =
      (1 - (1 / (q : ℝ)) ^ r) ^ 2 / (1 - (1 / (q : ℝ)) ^ (2 * r)) := by
    intro q _
    have h0 : 0 < (1 / (q : ℝ)) ^ r := pow_pos (inv_q_pos q) r
    have h1 : (1 / (q : ℝ)) ^ r < 1 := pow_inv_q_lt_one q (by omega)
    rw [pow_mul', sq]
    have : (1 : ℝ) - (1 / (q : ℝ)) ^ r * (1 / (q : ℝ)) ^ r =
        (1 - (1 / (q : ℝ)) ^ r) * (1 + (1 / (q : ℝ)) ^ r) := by ring
    rw [show ((1 / (q : ℝ)) ^ r) ^ 2 = (1 / (q : ℝ)) ^ r * (1 / (q : ℝ)) ^ r by ring, this]
    have h2 : (1 : ℝ) - (1 / (q : ℝ)) ^ r ≠ 0 := by linarith
    have h3 : (1 : ℝ) + (1 / (q : ℝ)) ^ r ≠ 0 := by linarith
    field_simp
  rw [prod_congr rfl hterm, prod_div_distrib, prod_pow]
  unfold correctionFactor
  rw [zetaN_eq N hr, zetaN_eq N (by omega : 2 ≤ 2 * r)]
  have hP : (∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ (2 * r))) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun q _ => sub_ne_zero.mpr (pow_inv_q_lt_one q (by omega)).ne')
  have hZ : zetaN ∅ (2 * r) ≠ 0 := (zetaN_pos ∅ (by omega)).ne'
  field_simp
end FixedOrderFactor
