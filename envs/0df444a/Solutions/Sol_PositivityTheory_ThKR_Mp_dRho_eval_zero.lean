-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.dRho_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:16.766713+00:00
-- url     : https://prove2.me/submissions/2421f1e0-a9a6-451b-8157-a424da6010b1

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_GlobalTheory_RealWeil_dRho_eq_sum
import Theorems.Thm_GlobalTheory_RealWeil_dRho_single_inl
import Theorems.Thm_GlobalTheory_RealWeil_dRho_single_inr
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
theorem _root_.solution (w : l ⊕ l → ℝ) (h : Sch l) :
    dRho w h 0 = ∑ a, (w (.inl a) : ℂ) * (∂_{(EuclideanSpace.single a 1 : Eu l)} h) 0 := by
  rw [dRho_eq_sum w]
  simp [Fintype.sum_sum_type, dRho_single_inl, dRho_single_inr]
end PositivityTheory.ThKR.Mp
