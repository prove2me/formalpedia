-- Prove2me | solution 1 for RobustMeanCov.Projection.standardize_mem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:25:44.734338+00:00
-- url     : https://prove2.me/submissions/f35c72c1-9671-4281-87da-f9cd1df4451a

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

theorem aux_stdz_sq (v : ℝ) (hv : 0 < v) : (v ^ (-(1 / 2 : ℝ))) ^ 2 * v = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

end RobustMeanCov.Projection

open RobustMeanCov.Projection

theorem solution (m v : ℝ) (hv : 0 < v) (ν : Measure ℝ) (hν : ν ∈ RobustMeanCov.Shared.MeanVarClass m v) :
    ν.map (fun r => v ^ (-(1 / 2 : ℝ)) * (r - m)) ∈ RobustMeanCov.Shared.MeanVarClass 0 1 := by
  obtain ⟨hP, hL, hmean, hvar⟩ := hν
  set c : ℝ := v ^ (-(1 / 2 : ℝ)) with hc
  have hmeas : Measurable (fun r : ℝ => c * (r - m)) := by fun_prop
  have hae : AEMeasurable (fun r : ℝ => c * (r - m)) ν := hmeas.aemeasurable
  have hint : Integrable (fun r : ℝ => r) ν := hL.integrable (by norm_num)
  have hL2 : MemLp (fun r : ℝ => c * (r - m)) 2 ν := (hL.sub (memLp_const m)).const_mul c
  refine ⟨Measure.isProbabilityMeasure_map hae, ?_, ?_, ?_⟩
  · rw [memLp_map_measure_iff (by fun_prop) hae]
    exact hL2
  · rw [integral_map hae (by fun_prop)]
    rw [integral_const_mul, integral_sub hint (integrable_const m), hmean]
    simp
  · rw [integral_map hae (by fun_prop)]
    simp only [sub_zero]
    have : (fun r : ℝ => (c * (r - m)) ^ 2) = fun r => c ^ 2 * (r - m) ^ 2 := by
      funext r; ring
    rw [this, integral_const_mul, hvar, hc]
    exact aux_stdz_sq v hv
