-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.AxImp.ex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:44.136278+00:00
-- url     : https://prove2.me/submissions/c5b86efe-ad05-49ff-8e9e-0c3fb10e2684

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
namespace AxImp
theorem _root_.solution (h : AxImp C ψ) {S : V R κ ≃ₗ[R] V R κ} (hS : IsSp S) : ∃ T, IsImp C ψ S T := by
  obtain ⟨T, h1, h2, h3, h4⟩ := h κ S hS
  exact ⟨T, h1, h2, h3, h4⟩
end AxImp
end PositivityTheory.ThKF0.Chr
