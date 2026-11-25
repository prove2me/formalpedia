-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Ax.box_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:41:47.210126+00:00
-- url     : https://prove2.me/submissions/8809cacf-461c-41b8-bfb1-aada0dd23fdc

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
import Theorems.Thm_PositivityTheory_ThKF0_Chr_rel_dv
import Theorems.Thm_PositivityTheory_ThKF0_Chr_schr_dv
import Theorems.Thm_PositivityTheory_ThKF0_Chr_ext_inl
import Theorems.Thm_PositivityTheory_ThKF0_Chr_ext_inr
import Theorems.Thm_P2M_PositivityTheory_ThKF0_Chr_extend_zero__0eec8e0f4aea
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_uniq
import Theorems.Thm_PositivityTheory_ThKF0_Chr_rel_lift
import Theorems.Thm_PositivityTheory_ThKF0_Chr_schr_zero
import Theorems.Thm_PositivityTheory_ThKF0_Chr_schrodinger_translate_apply


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
theorem _root_.solution (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e)
    (hE : IsE C ψ (dbS S) (Sum.map j j) E) : ∀ φ₂ ∈ C.sp κ, ∃ A ∈ C.sp κ₁, ∀ φ₁ ∈ C.sp κ, E (boxFun φ₁ φ₂) = boxFun (e φ₁) A := by
  intro φ₂ h₂
  have key : ∀ y : κ₁ → R, ∃ c : ℂ, ∀ φ₁ ∈ C.sp κ, ∀ x, E (boxFun φ₁ φ₂) (Sum.elim x y) = c * e φ₁ x := fun y => by
    set w := S.symm (Function.extend j y 0, Function.extend j 0 0) with hw
    have hr : Rel S j w (y, 0) := rel_lift hj (y, 0)
    have r0 : Rel S j 0 (0 : V R κ₁) := ⟨by simp [extend_zero' hj], by simp⟩
    have h₂' := h.schr κ (w.1, -w.2) φ₂ h₂
    obtain ⟨c, hc⟩ := h.uniq hS hj he (e' := Chr.res R Sum.inl ∘ₗ E ∘ₗ boxL κ (schr ψ (w.1, -w.2) φ₂)) (fun u u₁ hu φ hφ => by
      have e1 := hE.law _ _ ((rel_dv hj).2 ⟨hu, r0⟩) _ (h.box _ _ _ hφ _ h₂')
      rw [schr_dv, show (((0 : V R κ).1, -(0 : V R κ).2) : V R κ) = 0 by simp, schr_zero] at e1
      funext x
      show E (boxFun _ _) _ = schr ψ u₁ (fun x => E (boxFun _ _) (Function.extend Sum.inl x 0)) x
      rw [e1]
      simp only [schr, dv, ext_inl, sumElim_dotProduct_sumElim, ← Sum.elim_add_add]
      simp) (h.box_adm _ _ _ h₂' _ (hE.adm _ (h.res_adm _ _ _ Sum.inl_injective _ (h.ev0 _))))
    refine ⟨c, fun φ₁ h₁ x => ?_⟩
    have e1 := hE.law _ _ ((rel_dv hj).2 ⟨r0, hr⟩) _ (h.box _ _ _ h₁ _ h₂)
    rw [schr_dv, schr_zero] at e1
    have e2 : E (boxFun φ₁ _) (Function.extend Sum.inl x 0) = c * e φ₁ x := congrFun (hc φ₁ h₁) x
    rw [e1] at e2
    simpa [schr, dv, ext_inl, sumElim_dotProduct_sumElim, ← Sum.elim_add_add] using e2
  choose A hA using key
  obtain ⟨φ, hφ, h0⟩ := he.ne
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  have hx : e φ x ≠ 0 := hx
  refine ⟨A, ?_, fun φ₁ h₁ => funext fun z => ?_⟩
  · have := (C.sp κ₁).smul_mem (e φ x)⁻¹ (h.res _ _ _ Sum.inr_injective _
      (h.schr _ (Sum.elim x 0, 0) _ (hE.maps _ (h.box _ _ _ hφ _ h₂))))
    convert this using 1
    funext y
    rw [schrodinger_translate_apply]
    show _ = (e φ x)⁻¹ * E (boxFun φ φ₂) (Function.extend Sum.inr y 0 + Sum.elim x 0)
    rw [ext_inr, show (Sum.elim (0 : κ₁ → R) y + Sum.elim x (0 : κ₁ → R)) = Sum.elim x y by ext (k | k) <;> simp, hA y φ hφ]
    field_simp
  · rw [← Sum.elim_comp_inl_inr z, hA _ φ₁ h₁, mul_comm]
    rfl
end Ax
end PositivityTheory.ThKF0.Chr
