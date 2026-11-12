-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P76.highEnergyDispersionRatio
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:17:42.487619+00:00
-- url     : https://prove2.me/submissions/bce94482-c584-4ccc-a761-4745e5dc85ee

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo normalCDF normalQuantile)

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Intakenext100.P76 in
theorem solution :
    Tendsto (fun x : ℝ => thermalDispersion x / heterodyneDispersion x)
      atTop (𝓝 1) := by
  have hu := Real.tendsto_mul_log_one_add_div_atTop 1
  have hi : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h1 : Tendsto (fun x : ℝ => (1 + x⁻¹) ^ 3) atTop (𝓝 ((1 + 0) ^ 3)) :=
    (tendsto_const_nhds.add hi).pow 3
  have h2 : Tendsto (fun x : ℝ => 1 + 2 * x⁻¹) atTop (𝓝 (1 + 2 * 0)) :=
    tendsto_const_nhds.add (hi.const_mul 2)
  have hlim := ((hu.pow 2).mul h1).div h2 (by norm_num)
  have e : ((1 : ℝ) ^ 2 * (1 + 0) ^ 3 / (1 + 2 * 0)) = 1 := by norm_num
  rw [e] at hlim
  have hlog : ∀ x : ℝ, 0 < x → Real.log (x + 1) - Real.log x = Real.log (1 + 1 / x) := by
    intro x hx
    rw [← Real.log_div (by linarith) hx.ne', add_div, div_self hx.ne']
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  show (x * Real.log (1 + 1 / x)) ^ 2 * (1 + x⁻¹) ^ 3 / (1 + 2 * x⁻¹) =
    thermalDispersion x / heterodyneDispersion x
  rw [thermalDispersion, if_neg hx.ne', heterodyneDispersion, logTwo, logTwo, ← sub_div,
    hlog x hx]
  have hx0 : x ≠ 0 := hx.ne'
  have hx1 : x + 1 ≠ 0 := by linarith
  have hx2 : x + 2 ≠ 0 := by linarith
  have hL0 : Real.log 2 ≠ 0 := hL.ne'
  field_simp <;> ring
