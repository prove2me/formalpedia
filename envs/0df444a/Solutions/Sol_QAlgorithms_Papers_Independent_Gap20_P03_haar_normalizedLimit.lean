-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P03.haar_normalizedLimit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:39:17.950137+00:00
-- url     : https://prove2.me/submissions/31a6a614-f644-4c8c-af9b-1195aee34bb0

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable


theorem g73a_sumIcc2 (d : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.Icc 2 d, (i:ℝ)⁻¹) = (harmonic d : ℝ) - 1 := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  rw [← Finset.sum_erase_add (Finset.Icc 1 d) _ (Finset.left_mem_Icc.mpr hd)]
  simp [Finset.Icc_erase_left]
  congr 1

theorem g73a_ratio (d : ℕ) (hd : 2 ≤ d) :
    1 - 1 / Real.log d ≤ haarBound d / Real.logb 2 d ∧ haarBound d / Real.logb 2 d ≤ 1 := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (1:ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hlog : 0 < Real.log d := Real.log_pos hdpos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : haarBound d / Real.logb 2 d = (∑ i ∈ Finset.Icc 2 d, (i:ℝ)⁻¹) / Real.log d := by
    unfold haarBound Real.logb
    field_simp
  rw [hq, g73a_sumIcc2 d hd1]
  have h1 := log_add_one_le_harmonic d
  have h2 := harmonic_le_one_add_log d
  have h3 : Real.log d ≤ Real.log ((d+1:ℕ):ℝ) := by
    apply Real.log_le_log (by linarith); push_cast; linarith
  constructor
  · rw [le_div_iff₀ hlog]
    have : (1 - 1 / Real.log d) * Real.log d = Real.log d - 1 := by field_simp
    rw [this]; linarith
  · rw [div_le_one hlog]; linarith

/-- Appendix B, p.21: h_d/log_2(d) tends to one. The isolated quotient at d=1
has no effect on this atTop limit; no additive convergence is asserted. -/
theorem solution :
    Tendsto (fun d : ℕ => haarBound d / Real.logb 2 d) atTop (nhds 1) := by
  have hlog : Tendsto (fun d : ℕ => Real.log d) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun d : ℕ => 1 - 1 / Real.log d) atTop (nhds 1) := by
    have := (tendsto_inv_atTop_zero.comp hlog)
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hinv tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 2] with d hd using (g73a_ratio d hd).1
  · filter_upwards [eventually_ge_atTop 2] with d hd using (g73a_ratio d hd).2


end
