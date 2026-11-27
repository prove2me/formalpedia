-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.schr_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:22:35.603827+00:00
-- url     : https://prove2.me/submissions/13dfd460-47ee-422b-a512-8cfd5fde6f7b

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst

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
variable {R : Type} [CommRing R] [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}
  {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution (w : V R κ) (a : ℂ) (φ : (κ → R) → ℂ) : schr ψ w (a • φ) = a • schr ψ w φ := by
  funext z; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring
end PositivityTheory.ThKF0.Chr
