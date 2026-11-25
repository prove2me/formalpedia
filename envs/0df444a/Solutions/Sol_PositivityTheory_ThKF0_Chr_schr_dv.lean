-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.schr_dv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:56.735412+00:00
-- url     : https://prove2.me/submissions/2ce59b06-8799-461a-9818-780e015283a7

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
import Theorems.Thm_PositivityTheory_ThKF0_Chr_schr_box

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ κ₁ : Type}
variable [Fintype κ] [Fintype κ₁]
variable [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution (w w' : V R κ) (φ₁ φ₂ : (κ → R) → ℂ) :
    schr ψ (dv w w') (boxFun φ₁ φ₂) = boxFun (schr ψ w φ₁) (schr ψ (w'.1, -w'.2) φ₂) := schr_box w (w'.1, -w'.2) φ₁ φ₂
end PositivityTheory.ThKF0.Chr
