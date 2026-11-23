-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.rit_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:53:50.157929+00:00
-- url     : https://prove2.me/submissions/ae19caa4-63d7-4651-83e4-e3e8aab6fa51

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_rit_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) :
    ∀ (N : ℕ) (W : Fin N → M2 n), ContDiffOn ℂ ∞ (rit F N W) U := by
  intro N
  induction N with
  | zero => intro W; exact hF
  | succ N ih =>
    intro W
    rw [rit_succ]
    exact ((ih _).fderiv_of_isOpen hU (by simp)).clm_apply ((mulR (W 0)).contDiff.contDiffOn)
end PositivityTheory.Rg.Sw.LVs
