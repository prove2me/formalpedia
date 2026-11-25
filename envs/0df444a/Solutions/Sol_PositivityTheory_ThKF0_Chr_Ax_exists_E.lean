-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Ax.exists_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:52.923726+00:00
-- url     : https://prove2.me/submissions/7f6da8f6-1165-41ca-9727-b15ee3fff581

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Theorems.Thm_PositivityTheory_ThKF0_Chr_AxImp_ex
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_isE_res

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
namespace Ax
theorem _root_.solution (h : Ax C ψ) {S : V R κ ≃ₗ[R] V R κ} (hS : IsSp S) {j : κ₁ → κ} (hj : Function.Injective j) :
    ∃ e, IsE C ψ S j e := by
  obtain ⟨T, hT⟩ := h.imp.ex hS
  exact ⟨_, h.isE_res hT hj⟩
end Ax
end PositivityTheory.ThKF0.Chr
