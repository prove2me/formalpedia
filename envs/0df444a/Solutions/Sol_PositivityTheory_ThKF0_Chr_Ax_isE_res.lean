-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Ax.isE_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:19:12.783218+00:00
-- url     : https://prove2.me/submissions/b4a2e8ad-4fb0-4ed9-85db-c2b2a6c05d45

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Theorems.Thm_PositivityTheory_ThKF0_Chr_IsImp_cyc
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_cyc
import Theorems.Thm_P2M_PositivityTheory_ThKF0_Chr_extend_zero__0eec8e0f4aea
import Theorems.Thm_PositivityTheory_ThKF0_Chr_IsImp_law_res

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
theorem _root_.solution (h : Ax C ψ) {S : V R κ ≃ₗ[R] V R κ} {T : Module.End ℂ ((κ → R) → ℂ)} (hT : IsImp C ψ S T) {j : κ₁ → κ}
    (hj : Function.Injective j) : IsE C ψ S j (res R j ∘ₗ T) := by
  refine ⟨fun φ hφ => h.res _ _ j hj _ (hT.maps φ hφ), fun l hl => hT.adm _ (h.res_adm _ _ j hj l hl), hT.law_res hj, ?_⟩
  obtain ⟨φ, hφ, h0⟩ := h.ne κ
  obtain ⟨w, hw⟩ := hT.cyc hφ h0
  refine ⟨_, h.schr κ w φ hφ, fun e => hw ?_⟩
  have := congrFun e 0
  rwa [LinearMap.comp_apply, res, LinearMap.funLeft_apply, extend_zero' hj] at this
end Ax
end PositivityTheory.ThKF0.Chr
