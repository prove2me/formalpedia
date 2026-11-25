-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.unwBack_smooth_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:31:47.62901+00:00
-- url     : https://prove2.me/submissions/acbebf1b-f384-4e23-8a6b-e71f38d6355d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (u : M → ℝ)
    (hu : Smooth n z (fun y => (u y : ℂ))) : Smooth n z (fun y => (Real.exp (u y) : ℂ)) := by
  unfold Smooth at hu ⊢
  intro e he
  have hg : ContDiff ℝ ∞ (fun w : ℂ => ((Real.exp w.re : ℝ) : ℂ)) := by
    first
    | fun_prop
    | exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.reCLM.contDiff)
  refine (hg.comp_contDiffOn (hu e he)).congr fun p _ => ?_
  simp [Function.comp]
end ReciprocityTheory.L2DbarEstimates.F
