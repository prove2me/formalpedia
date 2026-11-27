-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.cmpa_det_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:36:30.965145+00:00
-- url     : https://prove2.me/submissions/0fb0ee15-6255-439d-ae56-3c0e9fa0df09

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaFderivCompApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaCHessComp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_cmpa_cHess_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_cmpa_det_jac

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
    (cHess n (h ∘ τ) x).det = (((‖(fderiv ℂ τ x).det‖ ^ 2 : ℝ)) : ℂ) * (cHess n h (τ x)).det := by
  rw [cmpa_cHess_comp hU hxU hτ hh, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hc : ((Matrix.of fun l j => (fderiv ℂ τ x (bas n j)) l).map conj).det =
      conj ((Matrix.of fun l j => (fderiv ℂ τ x (bas n j)) l).det) :=
    (RingHom.map_det (starRingEnd ℂ) _).symm
  rw [hc, cmpa_det_jac, Complex.sq_norm, ← Complex.mul_conj]
  ring
end ReciprocityTheory.L2DbarEstimates.Y
