-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.rit_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:17.644959+00:00
-- url     : https://prove2.me/submissions/24718667-85ea-4565-a0b1-b1c125fcb355

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_iterated_fderiv_right_translation
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_rit_zero
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
    ∀ (N : ℕ) (W : Fin N → M2 n), (∀ a b, W a * W b = 0) → ∀ x ∈ U,
      rit F N W x = iteratedFDeriv ℂ N F x (fun i => x * W i) := by
  intro N
  induction N with
  | zero =>
    intro W _ x _
    simp [rit_zero, iteratedFDeriv_zero_apply]
  | succ N ih =>
    intro W hW x hx
    rw [rit_succ]
    have hev : rit F N (fun i => W i.succ) =ᶠ[nhds x]
        (fun y => iteratedFDeriv ℂ N F y (fun i => y * W i.succ)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih _ (fun a b => hW _ _) y hy
    simp only
    rw [hev.fderiv_eq]
    exact iterated_fderiv_right_translation F U hU hF W hW x hx
end PositivityTheory.Rg.Sw.LVs
