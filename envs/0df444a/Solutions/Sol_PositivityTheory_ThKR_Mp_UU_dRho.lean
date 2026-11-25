-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.UU_dRho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:58.296379+00:00
-- url     : https://prove2.me/submissions/7d9ed741-ff0d-4d26-b47e-009cffd61ad4

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_PositivityTheory_ThKR_Mp_impl_UU
import Theorems.Thm_PositivityTheory_ThKR_Mp_isUnit_UU
import Theorems.Thm_PositivityTheory_ThKF_E_Impl_dRho


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR.Mp
theorem _root_.solution {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (w : l ⊕ l → ℝ) (f : Sch l) :
    UU S t (dRho w f) = dRho (nn S t *ᵥ w) (UU S t f) := by
  have hs : Function.Surjective (UU S t).toLinearMap := fun f => ⟨Ring.inverse (UU S t) f, by
    show (UU S t * Ring.inverse (UU S t)) f = f
    rw [Ring.mul_inverse_cancel _ (isUnit_UU S t), ContinuousLinearMap.one_apply]⟩
  exact Impl.dRho (s := Matrix.mulVecLin (nn S t)) (impl_UU hS t) hs w f
end PositivityTheory.ThKR.Mp
