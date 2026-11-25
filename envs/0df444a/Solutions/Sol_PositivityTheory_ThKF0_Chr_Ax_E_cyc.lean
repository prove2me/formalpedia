-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Ax.E_cyc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:19:06.98459+00:00
-- url     : https://prove2.me/submissions/927f094d-ba98-49fc-8ecf-cdf3bf430e0a

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Theorems.Thm_PositivityTheory_ThKF0_Chr_IsSp_trans
import Theorems.Thm_PositivityTheory_ThKF0_Chr_IsImp_cyc
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_cyc
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Law_inv
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Law_apply

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
variable {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e e' : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
namespace PositivityTheory.ThKF0.Chr
namespace Ax
theorem _root_.solution (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e) :
    Cyc C ψ (Chr.ev0 R κ₁ ∘ₗ e) := by
  refine h.cyc hS (he.adm _ (h.ev0 _)) (he.law.inv hj) ?_
  obtain ⟨φ, hφ, h0⟩ := he.ne
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  obtain ⟨w, hw⟩ := he.law.apply hj y
  exact ⟨_, h.schr κ w φ hφ, fun e0 => hy ((hw e he.law φ hφ).trans e0)⟩
end Ax
end PositivityTheory.ThKF0.Chr
