-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_isCuspidal_transportRep_37b7509b08da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:36:08.927928+00:00
-- url     : https://prove2.me/submissions/59b809d2-8403-4bac-b75a-7f504fc7ad2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCuspidalWithLabel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsTeichmullerMapAlgebraicClosureFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsIrreducibleTransportRep
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_transportRep_apply_3ef9cc1a238f
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_L2_NT_IsTeich_injective
import Theorems.Thm_GlobalTheory_FiniteGL_genericLine_apply
import Theorems.Thm_GlobalTheory_FiniteGL_isCuspidal_iff_twoBlocks
import Theorems.Thm_GlobalTheory_FiniteGL_mirabInduced_apply
import Theorems.Thm_GlobalTheory_FiniteGL_restrictMirab_apply
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply
attribute [local simp] GlobalTheory.FiniteGL.genericLine_apply
attribute [local simp] GlobalTheory.FiniteGL.mirabInduced_apply
attribute [local simp] GlobalTheory.FiniteGL.restrictMirab_apply
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv



set_option autoImplicit false
open Polynomial CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists
theorem _root_.solution {K : Type} [Field K] [Fintype K] [DecidableEq K] {N : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (τ : FDRep ℂ (GL (Fin N) K)) (h : Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ) (e : τ ≃ₗ[ℂ] W) :
    GlobalTheory.FiniteGL.IsCuspidal (transportRep τ.ρ e) := by
  rw [GlobalTheory.FiniteGL.isCuspidal_iff_twoBlocks]
  intro a ha haN w hw
  let b : Fin N → Fin 2 := fun i => if (i : ℕ) < a then 0 else 1
  have hs : Function.Surjective b := by
    intro c
    fin_cases c
    · exact ⟨⟨0, by omega⟩, by simp [b, ha]⟩
    · exact ⟨⟨a, haN⟩, by simp [b]⟩
  have h0 := h 2 b hs le_rfl (e.symm w) (fun u hu => ?_)
  · simpa using h0
  · obtain ⟨⟨hUT, -⟩, hdiag⟩ := hu
    have hu' : u ∈ GlobalTheory.FiniteGL.unipRadical K (GlobalTheory.FiniteGL.twoBlocks N a) := by
      intro i j hij
      have hlt : b i = b j ∨ b j < b i := by
        simp only [b, GlobalTheory.FiniteGL.twoBlocks] at hij ⊢
        split_ifs at hij ⊢ <;> simp_all
      rcases hlt with hb | hb
      · rw [Matrix.sub_apply, hdiag i j hb, Matrix.one_apply, sub_self]
      · have hne : i ≠ j := fun e' => by rw [e'] at hb; exact lt_irrefl _ hb
        rw [Matrix.sub_apply, hUT i j hb, Matrix.one_apply_ne hne, sub_zero]
    have h1 := hw u hu'
    rw [transportRep_apply] at h1
    apply e.injective
    rw [h1, e.apply_symm_apply]
end GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists
