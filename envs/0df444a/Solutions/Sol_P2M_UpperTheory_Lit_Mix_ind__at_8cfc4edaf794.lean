-- Prove2me | solution 1 for P2M_UpperTheory_Lit_Mix_ind__at_8cfc4edaf794
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:00:05.17324+00:00
-- url     : https://prove2.me/submissions/e952fae9-e1ea-4616-ac53-2a61d8a97231

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Definitions.Def_Development_AutomorphicArithmetic_ThetaCorrespondence_GeneralLinearGroups_MultiAt
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_continuous_relabel
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_isIrreducible_iff_of_linearEquiv
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_isUnitarisable_comp
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_comp
import Theorems.Thm_P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__iff_53a8980324c2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr ValuativeRel Matrix
open scoped TensorProduct
open UpperTheory UpperTheory.Lit UpperTheory.Lit.Mix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace UpperTheory.Lit.Mix
theorem _root_.solution (H : TwoAt k) (e : a ⊕ b ≃ n)
    {π₁ : Representation ℂ (GL a k) V} {π₂ : Representation ℂ (GL b k) W}
    (s₁ : IsSmooth π₁) (i₁ : π₁.IsIrreducible) (u₁ : IsUnitarisable π₁)
    (s₂ : IsSmooth π₂) (i₂ : π₂.IsIrreducible) (u₂ : IsUnitarisable π₂) :
    (ind₂ e (extTensor π₁ π₂)).IsIrreducible := by
  classical
  let ea := Fintype.equivFin a
  let eb := Fintype.equivFin b
  let f₁ : GL (Fin (Fintype.card a)) k →* GL a k := (relabel k ea).symm.toMonoidHom
  let f₂ : GL (Fin (Fintype.card b)) k →* GL b k := (relabel k eb).symm.toMonoidHom
  have c₁ : Continuous f₁ := continuous_relabel ea.symm
  have c₂ : Continuous f₂ := continuous_relabel eb.symm
  have i₁' : Representation.IsIrreducible (π₁.comp f₁ : Representation ℂ _ V) := by
    refine (isIrreducible_iff_of_linearEquiv (ρ := π₁) (σ := π₁.comp f₁) (relabel k ea)
      (relabel k ea).surjective (LinearEquiv.refl ℂ V) ?_).mp i₁
    intro g v
    simp [f₁]
  have i₂' : Representation.IsIrreducible (π₂.comp f₂ : Representation ℂ _ W) := by
    refine (isIrreducible_iff_of_linearEquiv (ρ := π₂) (σ := π₂.comp f₂) (relabel k eb)
      (relabel k eb).surjective (LinearEquiv.refl ℂ W) ?_).mp i₂
    intro g v
    simp [f₂]
  have h := H _ _ V W (π₁.comp f₁) (π₂.comp f₂) (isSmooth_comp s₁ f₁ c₁) i₁'
    (UnitInd.isUnitarisable_comp u₁ f₁) (isSmooth_comp s₂ f₂ c₂) i₂' (UnitInd.isUnitarisable_comp u₂ f₂)
  unfold prod₂ at h
  refine (isIrreducible_ind₂_iff e _ ea eb (LinearEquiv.refl ℂ _) ?_).mpr h
  intro g v
  simp [extTensor, f₁, f₂]
end UpperTheory.Lit.Mix
