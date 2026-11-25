-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.contract_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:30.040826+00:00
-- url     : https://prove2.me/submissions/e9dc3faf-6606-4299-875b-3b7900cf4b17

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContract
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_actT_reIx
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_actT_unc
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_core
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_reIx_smul
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_unc_cur
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_unc_inj
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_unc_smul
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
import Theorems.Thm_PositivityTheory_Rg_Cz_tE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open CtrX
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : TensorGl → QdetFacts → WallAlg → TensorGK → LieInv → WallQuot → Contract := by
  intro _ hQ hW hT hL hWQ
  intro n hn M _ _ ι _ _ Γ _ _ bar κ E ρ hK hG s φ hφ m hm hS
  classical
  obtain ⟨lab, c, ξ, hlab, hξ, I, w, hw, hφw⟩ := hS
  obtain ⟨N, F, hFgl, hFc, hFch, hFE, hN⟩ := hWQ n M ι E hG.gl hG.comm (fun _ _ => s) φ (by
    intro τ u; rw [hφ τ u]; simp [Finset.prod_const])
  obtain ⟨τ0, hτ0⟩ : ∃ τ0, lab ⟨0, hm⟩ = τ0 := ⟨_, rfl⟩
  let O := {p : Fin m // ¬ lab p = τ0}
  let e1 := Fintype.equivFin {p : Fin m // lab p = τ0}
  let e : Fin m ≃ O ⊕ Fin (Fintype.card {p : Fin m // lab p = τ0}) :=
    (Equiv.sumCompl (fun p : Fin m => lab p = τ0)).symm.trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCongr (Equiv.refl O) e1))
  let labO : O → ι := fun o => lab o.1
  have hle : lab ∘ e.symm = Sum.elim labO (fun _ => τ0) := by
    funext x
    rcases x with o | j
    · rfl
    · exact (e1.symm j).2
  have hm1 : 0 < Fintype.card {p : Fin m // lab p = τ0} := Fintype.card_pos_iff.2 ⟨⟨⟨0, hm⟩, hτ0⟩⟩
  set ζ := cur (reIx e ξ) with hζdef
  have hζS : ∀ γ, actT (fun _ : Fin (Fintype.card {p : Fin m // lab p = τ0}) => τ0) κ (actT labO κ ρ) γ ζ =
      (∏ τ, (κ τ γ).det ^ c τ) • ζ := by
    intro γ
    apply unc_inj
    rw [← actT_unc, unc_smul, hζdef, unc_cur, ← hle, actT_reIx, hξ γ, reIx_smul]
  obtain ⟨hGO, -⟩ := hT n M ι Γ bar κ E ρ hK hG O labO
  let I0 : O → Fin n := I ∘ e.symm ∘ Sum.inl
  let q : TV n M O →ₗ[ℂ] M ⧸ N := N.mkQ ∘ₗ LinearMap.proj I0
  have hf0 : fib labO τ0 = ∅ := by
    ext o
    simp [fib, labO, o.2]
  have hf1 : fib labO (bar τ0) = ∅ := by
    ext o
    have := hlab o.1 ⟨0, hm⟩
    rw [hτ0] at this
    simp [fib, labO, this]
  have hq : ∀ τ, fib labO τ = ∅ → ∀ a b, q ∘ₗ tE (fib labO τ) (E τ) a b = F τ a b ∘ₗ q := by
    intro τ h a b
    apply LinearMap.ext
    intro f
    show N.mkQ (tE (fib labO τ) (E τ) a b f I0) = F τ a b (N.mkQ (f I0))
    rw [tE_apply, h, Finset.sum_empty, add_zero]
    exact LinearMap.congr_fun (hFE τ a b) (f I0)
  have hξN : ξ I ∉ N := by
    intro h
    exact hφw ((hN _).1 h w hw)
  have hz : q (ζ (I ∘ e.symm ∘ Sum.inr)) ≠ 0 := by
    have h3 : Sum.elim (I ∘ e.symm ∘ Sum.inl) (I ∘ e.symm ∘ Sum.inr) = I ∘ e.symm :=
      Sum.elim_comp_inl_inr (I ∘ e.symm)
    have h4 : ζ (I ∘ e.symm ∘ Sum.inr) I0 = ξ I := by
      simp only [hζdef, cur, reIx, I0, h3]
      congr 1
      funext i
      simp
    show N.mkQ (ζ (I ∘ e.symm ∘ Sum.inr) I0) ≠ 0
    rw [h4, Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
    exact hξN
  obtain ⟨m2, hm2, ζ2, hζ2, I2, hI2⟩ := core hQ hW hT hL hK hGO τ0 q (F τ0) (F (bar τ0)) s (hFgl _) (hFgl _)
    (hFc _ _ (Ne.symm (hK.ne τ0))) (hFch τ0) (hFch (bar τ0)) (hq τ0 hf0) (hq _ hf1) hn _ hm1 c ζ hζS
    ⟨_, hz⟩
  let e3 := Fintype.equivFin (O ⊕ Fin m2)
  have hcard : m = Fintype.card O + Fintype.card {p : Fin m // lab p = τ0} := by
    have := Fintype.card_congr e
    simpa [Fintype.card_sum] using this
  refine ⟨Fintype.card (O ⊕ Fin m2), ?_, (Sum.elim labO (fun _ => τ0)) ∘ e3.symm,
    Function.update c τ0 (c τ0 - 1), reIx e3 (unc ζ2), ?_, ?_, ?_⟩
  · rw [Fintype.card_sum, Fintype.card_fin]
    omega
  · have hex : ∀ x : O ⊕ Fin m2, ∃ p, Sum.elim labO (fun _ => τ0) x = lab p := by
      rintro (o | j)
      · exact ⟨o.1, rfl⟩
      · exact ⟨⟨0, hm⟩, hτ0.symm⟩
    intro p p'
    obtain ⟨r, hr⟩ := hex (e3.symm p)
    obtain ⟨r', hr'⟩ := hex (e3.symm p')
    simp only [Function.comp_apply]
    rw [hr, hr']
    exact hlab r r'
  · intro γ
    rw [actT_reIx, actT_unc, hζ2 γ, unc_smul, reIx_smul]
  · have hv : reIx e3 (unc ζ2) (Sum.elim I0 I2 ∘ e3.symm) = ζ2 I2 I0 := by
      show unc ζ2 ((Sum.elim I0 I2 ∘ e3.symm) ∘ e3) = _
      rw [show (Sum.elim I0 I2 ∘ e3.symm) ∘ e3 = Sum.elim I0 I2 from by funext x; simp]
      rfl
    have hnot : ζ2 I2 I0 ∉ N := by
      have h5 : N.mkQ (ζ2 I2 I0) ≠ 0 := hI2
      rwa [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero] at h5
    rw [hN] at hnot
    push_neg at hnot
    obtain ⟨w', hw', hφ'⟩ := hnot
    exact ⟨_, w', hw', by rwa [hv]⟩
end PositivityTheory.Rg.Cz
