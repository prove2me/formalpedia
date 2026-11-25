-- Prove2me | solution 1 for P2M_GlobalTheory_SmGL_Stages_ind__assoc_9f771f8b94ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:32:06.218857+00:00
-- url     : https://prove2.me/submissions/d6a2e228-5a9d-42d9-8108-88e27aafe3d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
import Theorems.Thm_GlobalTheory_SmGL_Stages_pr_fst
import Theorems.Thm_GlobalTheory_SmGL_Stages_pr_snd
import Theorems.Thm_GlobalTheory_SmGL_Stages_stage_fst
import Theorems.Thm_GlobalTheory_SmGL_Stages_stage_snd
import Theorems.Thm_GlobalTheory_SmGL_Stages_action_eq
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_mem_parab_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c ab bc n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype ab] [DecidableEq ab] [Fintype bc] [DecidableEq bc] [Fintype n] [DecidableEq n]
  {W V₁ V₂ V₃ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]
namespace GlobalTheory.SmGL.Stages
theorem _root_.solution (e₁ : ab ⊕ c ≃ n) (f₁ : a ⊕ b ≃ ab) (e₂ : a ⊕ bc ≃ n) (f₂ : b ⊕ c ≃ bc)
    (Ha : ∀ i, e₁ (.inl (f₁ (.inl i))) = e₂ (.inl i))
    (Hb : ∀ i, e₁ (.inl (f₁ (.inr i))) = e₂ (.inr (f₂ (.inl i))))
    (Hc : ∀ i, e₁ (.inr i) = e₂ (.inr (f₂ (.inr i))))
    (π₁ : Representation ℂ (GL a k) V₁) (π₂ : Representation ℂ (GL b k) V₂)
    (π₃ : Representation ℂ (GL c k) V₃) :
    Nonempty ((ind₂ e₁ (extTensor (ind₂ f₁ (extTensor π₁ π₂)) π₃)).Equiv
      (ind₂ e₂ (extTensor π₁ (ind₂ f₂ (extTensor π₂ π₃))))) := by
  let R : Subgroup (GL n k) := parab k (two e₁) ⊓ parab k (two e₂)
  have hR₁ : ∀ q : parab k (two e₁), (q : GL n k) ∈ R ↔ (pr e₁ q).1 ∈ parab k (two f₁) := fun q => by
    refine ⟨fun h => (mem_parab_two k).2 fun j i => ?_,
      fun h => ⟨q.2, (mem_parab_two k).2 fun j i => ?_⟩⟩
    · rw [pr_fst, Ha, Hb]
      exact (mem_parab_two k).1 h.2 _ _
    · obtain ⟨j | j, rfl⟩ := f₂.surjective j
      · rw [← Ha, ← Hb]
        exact (mem_parab_two k).1 h j i
      · rw [← Ha, ← Hc]
        exact (mem_parab_two k).1 q.2 _ _
  have hR₂ : ∀ q : parab k (two e₂), (q : GL n k) ∈ R ↔ (pr e₂ q).2 ∈ parab k (two f₂) := fun q => by
    refine ⟨fun h => (mem_parab_two k).2 fun j i => ?_,
      fun h => ⟨(mem_parab_two k).2 fun j i => ?_, q.2⟩⟩
    · rw [pr_snd, ← Hc, ← Hb]
      exact (mem_parab_two k).1 h.1 _ _
    · obtain ⟨i | i, rfl⟩ := f₁.surjective i
      · rw [Ha, Hc]
        exact (mem_parab_two k).1 q.2 _ _
      · rw [Hb, Hc]
        exact (mem_parab_two k).1 h j i
  let ι₁ : R →* parab k (two e₁) := Subgroup.inclusion inf_le_left
  let ρ : Representation ℂ R ((V₁ ⊗[ℂ] V₂) ⊗[ℂ] V₃) :=
    Representation.tprod ((dat f₁ (extTensor π₁ π₂)).comp
      ((((MonoidHom.fst _ _).comp (pr e₁)).comp ι₁).codRestrict _ fun r => (hR₁ (ι₁ r)).1 r.2))
      ((tauSnd e₁ π₃).comp ι₁)
  have hρ : ∀ (g : GL n k) (h : g ∈ R), ρ ⟨g, h⟩ = TensorProduct.map
      (dat f₁ (extTensor π₁ π₂) ⟨(pr e₁ ⟨g, h.1⟩).1, (hR₁ ⟨g, h.1⟩).1 h⟩) (tauSnd e₁ π₃ ⟨g, h.1⟩) :=
    fun g h => rfl
  have E₁ := stage_fst e₁ f₁ (R := R) inf_le_left hR₁ (dat f₁ (extTensor π₁ π₂)) π₃ ρ (.refl _ _)
    (fun q h z => by rw [hρ]; rfl)
  have E₂ := stage_snd e₂ f₂ (R := R) inf_le_right hR₂ (dat f₂ (extTensor π₂ π₃)) π₁ ρ
    ((TensorProduct.comm _ _ _).trans (TensorProduct.assoc _ _ _ _).symm)
    (fun q h z => by
      rw [hρ]
      exact action_eq e₁ f₁ e₂ f₂ Ha Hb Hc π₁ π₂ π₃ _ q _ _ rfl rfl rfl z)
  exact Nonempty.map2 (fun x y => x.trans y.symm) E₁ E₂
end GlobalTheory.SmGL.Stages
