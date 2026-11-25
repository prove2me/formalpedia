-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.schr_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:03:04.592477+00:00
-- url     : https://prove2.me/submissions/6fb8b2f6-706e-496e-b788-a16fe0543321

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
theorem _root_.solution (φ : (κ → R) → ℂ) : schr ψ (0 : V R κ) φ = φ := by
  funext z; simp [schr]
end PositivityTheory.ThKF0.Chr
