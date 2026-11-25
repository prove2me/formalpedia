-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Ax.comp_cyc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:27:54.572905+00:00
-- url     : https://prove2.me/submissions/2db9e537-357f-4934-8b83-fe2d2f9b50c5

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Theorems.Thm_PositivityTheory_ThKF0_Chr_rel_lift
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_E_cyc

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
theorem _root_.solution (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e)
    {l : ((κ₁ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : Cyc C ψ l) : ∀ φ ∈ C.sp κ, φ ≠ 0 → ∃ w w', l (e (schr ψ w' (schr ψ w φ))) ≠ 0 := by
  intro φ hφ h0
  obtain ⟨w, hw⟩ := h.E_cyc hS hj he φ hφ h0
  have hs := h.schr κ w φ hφ
  obtain ⟨w₁, hw₁⟩ := hl _ (he.maps _ hs) fun e0 => hw (congrFun e0 0)
  exact ⟨w, _, by rwa [he.law _ w₁ (rel_lift hj _) _ hs]⟩
end Ax
end PositivityTheory.ThKF0.Chr
