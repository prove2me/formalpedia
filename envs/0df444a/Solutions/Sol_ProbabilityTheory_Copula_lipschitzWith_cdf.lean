-- Prove2me | solution 1 for ProbabilityTheory.Copula.lipschitzWith_cdf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:48:46.784942+00:00
-- url     : https://prove2.me/submissions/3f17b6af-b21e-4cd8-a5e5-71c86600c762

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_CDF_Continuity
public import Theorems.Thm_ProbabilityTheory_Copula_abs_cdf_sub_le_sum_abs
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_dim_zero
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_update_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_zero
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
public import Theorems.Thm_ProbabilityTheory_Copula_measureReal_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_measure_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_ofMap
attribute [local simp] ProbabilityTheory.Copula.cdf_dim_zero
attribute [local simp] ProbabilityTheory.Copula.cdf_one
attribute [local simp] ProbabilityTheory.Copula.cdf_update_one
attribute [local simp] ProbabilityTheory.Copula.cdf_zero
attribute [local simp] ProbabilityTheory.Copula.map_eval
attribute [local simp] ProbabilityTheory.Copula.measureReal_eval_le
attribute [local simp] ProbabilityTheory.Copula.measure_eval_le
attribute [local simp] ProbabilityTheory.Copula.toMeasure_ofMap



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval BigOperators NNReal
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) : LipschitzWith (d : ℝ≥0) C.cdf := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  calc
    dist (C.cdf u) (C.cdf v) = |C.cdf u - C.cdf v| := Real.dist_eq _ _
    _ ≤ ∑ i, |(u i : ℝ) - (v i : ℝ)| := C.abs_cdf_sub_le_sum_abs u v
    _ ≤ ∑ _ : Fin d, dist u v := Finset.sum_le_sum fun i _ => by
      simpa [Subtype.dist_eq, Real.dist_eq] using dist_le_pi_dist u v i
    _ = (d : ℝ≥0) * dist u v := by simp
end ProbabilityTheory.Copula
