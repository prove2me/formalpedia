-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.IsSp.trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:43.758021+00:00
-- url     : https://prove2.me/submissions/bf5cb108-3f98-4a0a-9e4d-7a50685e6a63

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
omit [Invertible (2 : R)]
namespace PositivityTheory.ThKF0.Chr
namespace IsSp
theorem _root_.solution {S S' : V R κ ≃ₗ[R] V R κ} (h : IsSp S) (h' : IsSp S') : IsSp (S.trans S') := fun w w' =>
  (h' (S w) (S w')).trans (h w w')
end IsSp
end PositivityTheory.ThKF0.Chr
