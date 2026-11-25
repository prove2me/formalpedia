-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flA_diff_comp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:19:25.313854+00:00
-- url     : https://prove2.me/submissions/382da38b-d8ca-44b1-acb8-217d667d1633

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA

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
theorem _root_.solution {G : V n → V n} {y : V n} (hG : ContDiffAt ℂ 2 G y) (k b : Fin n) :
    DifferentiableAt ℂ (fun v => fderiv ℂ G v (bas n k) b) y := by
  have hD1 : DifferentiableAt ℂ (fderiv ℂ G) y :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact (EuclideanSpace.proj b : V n →L[ℂ] ℂ).differentiableAt.comp y
    (hD1.clm_apply (differentiableAt_const _))
end ReciprocityTheory.L2DbarEstimates.Y
