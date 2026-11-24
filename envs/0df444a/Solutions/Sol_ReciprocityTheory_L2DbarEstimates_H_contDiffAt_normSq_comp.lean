-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.contDiffAt_normSq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:59.074619+00:00
-- url     : https://prove2.me/submissions/7b6fc9c1-17d1-4f55-9960-e427a7fd9ee8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    ContDiffAt ℝ 2 (fun y => Complex.normSq (g y)) x := by
  have h1 : ContDiffAt ℝ 2 g x := hg.restrict_scalars ℝ
  have h2 : ContDiffAt ℝ 2 (fun y => ‖g y‖ ^ 2) x := by
    first
    | exact (contDiff_norm_sq ℝ).contDiffAt.comp x h1
    | exact (contDiff_norm_sq ℂ).contDiffAt.comp x h1
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  exact Complex.normSq_eq_norm_sq _
end ReciprocityTheory.L2DbarEstimates.H
