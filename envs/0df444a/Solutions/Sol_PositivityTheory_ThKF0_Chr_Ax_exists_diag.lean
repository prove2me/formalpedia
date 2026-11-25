-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Ax.exists_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:00.769752+00:00
-- url     : https://prove2.me/submissions/561d75e1-8e6f-4d69-aa0a-75921e404ae7

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
import Theorems.Thm_PositivityTheory_ThKF0_Chr_kE_dv
import Theorems.Thm_PositivityTheory_ThKF0_Chr_isSp_kE
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_exists_form


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
variable {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
  {E : ((κ ⊕ κ → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ₁ → R) → ℂ)}
namespace PositivityTheory.ThKF0.Chr
namespace Ax
theorem _root_.solution (h : Ax C ψ) (κ : Type) [Fintype κ] : ∃ l ∈ C.adm (κ ⊕ κ),
    (∀ w : V R κ, ∀ φ ∈ C.sp (κ ⊕ κ), l (schr ψ (dv w w) φ) = l φ) ∧ Cyc C ψ l := by
  obtain ⟨l, h1, h2, h3⟩ := h.exists_form (isSp_kE (R := R) fun _ : κ => True)
  exact ⟨l, h1, fun w => h2 _ (by rw [kE_dv]; ext (k | k) <;> simp), h3⟩
end Ax
end PositivityTheory.ThKF0.Chr
