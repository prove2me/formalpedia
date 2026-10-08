-- Prove2me | solution 1 for OnlineRandomization.Tightness.params_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T11:43:03.300805+00:00
-- url     : https://prove2.me/submissions/b28aa1c3-5677-45fe-bd82-43236ef01666

import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model
import Definitions.Def_OnlineRandomization_Tightness_MatesGame

open Filter Topology OnlineRandomization.Tightness in
theorem solution (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (paramSmall α β) atTop (𝓝 β) ∧
      Tendsto (paramLarge α β) atTop (𝓝 (α * β)) := by
  have hu : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  constructor
  · have hc : ContinuousAt (fun u : ℝ => (4 * β - (2 + 2 * β) * u + (2 - 2 * α) * u ^ 2) /
        (4 + (2 * α - 6) * u + (2 - 2 * α) * u ^ 2)) 0 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      norm_num
    have hg : Tendsto (fun u : ℝ => (4 * β - (2 + 2 * β) * u + (2 - 2 * α) * u ^ 2) /
        (4 + (2 * α - 6) * u + (2 - 2 * α) * u ^ 2)) (𝓝 0) (𝓝 β) := by
      have h := hc.tendsto
      convert h using 2
      norm_num
    refine (hg.comp hu).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with t ht
    have ht' : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    have ht0 : (t : ℝ) ≠ 0 := by positivity
    have h1 : (2 * (t : ℝ) - 2) ≠ 0 := by linarith
    have h2 : (α + 2 * (t : ℝ) - 1) ≠ 0 := by linarith
    have hD : (4 + (2 * α - 6) * (t : ℝ)⁻¹ + (2 - 2 * α) * ((t : ℝ)⁻¹) ^ 2) =
        ((2 * (t : ℝ) - 2) * (α + 2 * (t : ℝ) - 1)) * ((t : ℝ)⁻¹) ^ 2 := by
      field_simp
      ring
    have hN : (4 * β - (2 + 2 * β) * (t : ℝ)⁻¹ + (2 - 2 * α) * ((t : ℝ)⁻¹) ^ 2) =
        (1 + (2 * (t : ℝ) - 1) * (2 * (t : ℝ) * β - 1) - 2 * α) * ((t : ℝ)⁻¹) ^ 2 := by
      field_simp
      ring
    simp only [Function.comp, paramSmall]
    rw [hD, hN, mul_div_mul_right _ _ (by positivity)]
  · have hc : ContinuousAt (fun u : ℝ => (2 * α * β + (α - 1) * u) / (2 + (α - 1) * u)) 0 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      norm_num
    have hg : Tendsto (fun u : ℝ => (2 * α * β + (α - 1) * u) / (2 + (α - 1) * u))
        (𝓝 0) (𝓝 (α * β)) := by
      have h := hc.tendsto
      convert h using 2
      norm_num
      ring
    refine (hg.comp hu).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    have ht0 : (t : ℝ) ≠ 0 := by positivity
    have hD : (2 + (α - 1) * (t : ℝ)⁻¹) = (α + 2 * (t : ℝ) - 1) * (t : ℝ)⁻¹ := by
      field_simp
      ring
    have hN : (2 * α * β + (α - 1) * (t : ℝ)⁻¹) =
        (2 * (t : ℝ) * α * β + α - 1) * (t : ℝ)⁻¹ := by
      field_simp
      ring
    simp only [Function.comp, paramLarge]
    rw [hD, hN, mul_div_mul_right _ _ (by positivity)]
