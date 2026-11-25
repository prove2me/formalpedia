-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.cmpa_cHess_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:27:17.971657+00:00
-- url     : https://prove2.me/submissions/43ea8b81-02de-4d8d-993c-4a6e0316cea8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaFderivCompApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaCHessComp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_cmpa_hess_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {τ : V n → V n} {h : V n → ℂ} {x : V n} {U : Set (V n)} (hU : IsOpen U)
    (hxU : x ∈ U) (hτ : DifferentiableOn ℂ τ U) (hh : ContDiffAt ℝ 2 h (τ x)) :
    cHess n (h ∘ τ) x = (Matrix.of fun l j => (fderiv ℂ τ x (bas n j)) l).transpose * cHess n h (τ x) *
      (Matrix.of fun l j => (fderiv ℂ τ x (bas n j)) l).map conj := by
  ext j k
  simp only [cHess, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [cmpa_hess_comp hU hxU hτ hh j k]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring
end ReciprocityTheory.L2DbarEstimates.Y
