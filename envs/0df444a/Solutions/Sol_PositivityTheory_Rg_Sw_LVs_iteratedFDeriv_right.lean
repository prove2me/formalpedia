-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.iteratedFDeriv_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:11.216362+00:00
-- url     : https://prove2.me/submissions/842f6f35-83e7-4901-928c-9cf20dad9b42

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_iterated_fderiv_right_translation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {N : ℕ} (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (W : Fin (N + 1) → M2 n) (hW : ∀ a b, W a * W b = 0) (x : M2 n) (hx : x ∈ U) :
    fderiv ℂ (fun y => iteratedFDeriv ℂ N F y (fun i => y * W i.succ)) x (x * W 0) =
      iteratedFDeriv ℂ (N + 1) F x (fun i => x * W i) :=
  iterated_fderiv_right_translation F U hU hF W hW x hx
end PositivityTheory.Rg.Sw.LVs
