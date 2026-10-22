-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P36.thermalLaw_thinning
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:25:07.068993+00:00
-- url     : https://prove2.me/submissions/1051b125-7c3e-40ca-97f8-86e483f94621

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P36
noncomputable section

open QAlgorithms.Papers.Independent.Claimed50.P36

open Filter

open scoped Topology ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable

-- Reuse the pinned accepted entropy definitions, preserving their codomains
-- and units. P24.bosonicEntropy is in bits: multiply by log 2 for nats.
-- P01.binaryEntropy is in nats and ENNReal-valued: use toReal only at the
-- finite binary-probability argument of binaryValue below.

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

set_option maxHeartbeats 1000000 in
theorem solution (eta m : ℝ)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (hm : 0 ≤ m) :
    ∀ y : ℕ, HasSum (fun n => thermalLaw m n * lossTransition eta n y)
      (thermalLaw (eta * m) y) := by
  intro y
  set q : ℝ := m / (1 + m) with hq
  have hm1 : 0 < 1 + m := by linarith
  have hq0 : 0 ≤ q := div_nonneg hm (by linarith)
  have hq1 : q < 1 := (div_lt_one hm1).2 (by linarith)
  set r : ℝ := q * (1 - eta) with hr
  have hr0 : 0 ≤ r := mul_nonneg hq0 (by linarith)
  have hr1 : r < 1 := by
    calc r = q * (1 - eta) := rfl
      _ ≤ q * 1 := mul_le_mul_of_nonneg_left (by linarith) hq0
      _ < 1 := by linarith
  have hgeo := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) y
    (show ‖r‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  set C : ℝ := 1 / (1 + m) * (q * eta) ^ y with hC
  have hshift : HasSum (fun k : ℕ => thermalLaw m (k + y) * lossTransition eta (k + y) y)
      (C * (1 / (1 - r) ^ (y + 1))) := by
    refine (hgeo.mul_left C).congr_fun fun k => ?_
    simp only [thermalLaw, lossTransition, if_pos (Nat.le_add_left y k), Nat.add_sub_cancel]
    rw [← hq, hC, hr, mul_pow, mul_pow, pow_add, show k + y = y + k from add_comm k y, Nat.choose_symm_add]
    ring
  have hzero : ∀ i ∈ Finset.range y, thermalLaw m i * lossTransition eta i y = 0 := by
    intro i hi
    have : ¬ y ≤ i := by simpa using hi
    simp [lossTransition, this]
  have h2 : HasSum (fun n => thermalLaw m n * lossTransition eta n y) (C * (1 / (1 - r) ^ (y + 1))) := by
    rw [← hasSum_nat_add_iff' y, Finset.sum_eq_zero hzero, sub_zero]
    exact hshift
  convert h2 using 1
  -- algebra: value
  have h1r : 1 - r = (1 + eta * m) / (1 + m) := by
    simp only [hr, hq]; field_simp; ring
  have hem : 0 < 1 + eta * m := by nlinarith
  rw [h1r, hC, hq, thermalLaw]
  simp only [div_pow, mul_pow, pow_succ]
  field_simp

end
