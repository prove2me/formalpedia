-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_isIrreducible_transportRep_d83896ad2d55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:49:27.137789+00:00
-- url     : https://prove2.me/submissions/a75bd410-4449-47a2-928e-9e359244fee4

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
import Theorems.Thm_GlobalTheory_FiniteGL_genericLine_apply
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
theorem _root_.solution {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) (hV : Nontrivial V)
    (h : ∀ U : Submodule ℂ V, (∀ g, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤) : (transportRep ρ e).IsIrreducible := by
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨e.symm.toEquiv.nontrivial, fun U hU => ?_⟩
  have hinv : ∀ g, ∀ v ∈ U.comap e.toLinearMap, ρ g v ∈ U.comap e.toLinearMap := by
    intro g v hv
    have h1 := hU g (e v) hv
    rw [transportRep_apply, e.symm_apply_apply] at h1
    exact h1
  rcases h _ hinv with h0 | h0
  · left
    refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
    have h1 : e.symm w ∈ U.comap e.toLinearMap := by
      show e (e.symm w) ∈ U
      rwa [e.apply_symm_apply]
    rw [h0, Submodule.mem_bot] at h1
    simpa using h1
  · right
    refine (Submodule.eq_top_iff').2 fun w => ?_
    have h1 : e.symm w ∈ U.comap e.toLinearMap := by rw [h0]; trivial
    have h2 : e (e.symm w) ∈ U := h1
    rwa [e.apply_symm_apply] at h2
end GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists
