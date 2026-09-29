-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.comp_eq_one_iff_comp_eq_one_of_finrank_eq_of_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c2ee5376-2bc9-59e1-9fc9-5eb8953b17ac

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_comp_eq_one_iff_comp_eq_one_of_finrank_eq_of_isClosedImmersion

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassProjModel NeronModelInfra WeierstrassCurve.DrinfeldGlobal

namespace KerAgreeAsm

theorem comp_eq_one_iff_exists_fac
    {T : Type} [CommRing T] {E₁ E₂ : Scheme} {s₁ : E₁ ⟶ Spec (CommRingCat.of T)} {s₂ : E₂ ⟶ Spec (CommRingCat.of T)}
    (G₁ : RelativeGroupLaw T s₁) (G₂ : RelativeGroupLaw T s₂)
    (f : E₁ ⟶ E₂) (hf : f ≫ s₂ = s₁)
    (hfhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t s₁),
      (⟨(G₁.mul t x y).1 ≫ f, by rw [Category.assoc, hf]; exact (G₁.mul t x y).2⟩ : SchemeHomOver t s₂) =
        G₂.mul t ⟨x.1 ≫ f, by rw [Category.assoc, hf]; exact x.2⟩ ⟨y.1 ≫ f, by rw [Category.assoc, hf]; exact y.2⟩)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    (m : ℕ) (hfrk : ∀ p, f.finrank p = m)
    (K : Scheme) (ι : K ⟶ E₁) [IsClosedImmersion ι] [Flat (ι ≫ s₁)] [LocallyOfFinitePresentation (ι ≫ s₁)]
    (hKrk : ∀ s, (ι ≫ s₁).finrank s = m)
    (hKf : ι ≫ f = (ι ≫ s₁) ≫ (G₂.one (𝟙 _)).1)
    [IsSeparated s₂]
    {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x : SchemeHomOver t s₁) :
    (⟨x.1 ≫ f, by rw [Category.assoc, hf]; exact x.2⟩ : SchemeHomOver t s₂) = G₂.one t ↔ ∃ z : S ⟶ K, x.1 = z ≫ ι := by
  set e : Spec (CommRingCat.of T) ⟶ E₂ := (G₂.one (𝟙 _)).1 with he
  have hes : e ≫ s₂ = 𝟙 _ := (G₂.one (𝟙 _)).2

  have hone : (G₂.one t).1 = t ≫ e := by
    rw [← G₂.one_natural (𝟙 _) t t (Category.comp_id t)]
    rfl

  haveI : IsClosedImmersion e := by
    have : IsClosedImmersion (e ≫ s₂) := by rw [hes]; infer_instance
    exact IsClosedImmersion.of_comp e s₂

  haveI : IsFinite (pullback.snd f e) := MorphismProperty.pullback_snd _ _ inferInstance
  haveI : Flat (pullback.snd f e) := MorphismProperty.pullback_snd _ _ inferInstance
  haveI : LocallyOfFinitePresentation (pullback.snd f e) := MorphismProperty.pullback_snd _ _ inferInstance
  have hkrk : ∀ s, (pullback.snd f e).finrank s = m := by
    intro s
    have h := WeierstrassProjModel.RelativeGroupLaw.finrank_eq_finrank_pullback_snd_one_of_hom G₁ G₂ f hf hfhom (e.base s)
    rw [hfrk] at h
    have hb : s₂.base (e.base s) = s := by
      change (e ≫ s₂).base s = s
      rw [hes]
      rfl
    rw [hb] at h
    exact h.symm

  set κ : K ⟶ pullback f e := pullback.lift ι (ι ≫ s₁) (by rw [hKf]) with hκ
  have hκfst : κ ≫ pullback.fst f e = ι := pullback.lift_fst _ _ _
  have hκsnd : κ ≫ pullback.snd f e = ι ≫ s₁ := pullback.lift_snd _ _ _
  haveI : IsClosedImmersion (pullback.fst f e) := MorphismProperty.pullback_fst _ _ inferInstance
  haveI : IsClosedImmersion κ := by
    have : IsClosedImmersion (κ ≫ pullback.fst f e) := by rw [hκfst]; infer_instance
    exact IsClosedImmersion.of_comp κ (pullback.fst f e)
  haveI hiso : IsIso κ :=
    AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq κ (pullback.snd f e) (ι ≫ s₁) hκsnd
      (fun s => by rw [hKrk, hkrk])
  constructor
  · intro hx1
    have hx1' : x.1 ≫ f = t ≫ e := by
      have := congrArg Subtype.val hx1
      rw [hone] at this
      exact this
    refine ⟨pullback.lift x.1 t hx1' ≫ inv κ, ?_⟩
    rw [Category.assoc, ← hκfst, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  · rintro ⟨z, hz⟩
    apply Subtype.ext
    rw [hone]
    show x.1 ≫ f = t ≫ e
    rw [hz, Category.assoc, hKf, ← x.2, hz]
    simp only [Category.assoc]

end KerAgreeAsm

open KerAgreeAsm in
theorem solution
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type) [CommRing T] [Algebra A T]
    (W₁ W₂ W₃ : WeierstrassCurve T) (hΔ₁ : IsUnit W₁.Δ) (hΔ₂ : IsUnit W₂.Δ) (hΔ₃ : IsUnit W₃.Δ)
    (f : projModelCR W₁.toProjective ⟶ projModelCR W₂.toProjective)
    (hf : f ≫ projModelStrCR W₂.toProjective = projModelStrCR W₁.toProjective)
    (g : projModelCR W₁.toProjective ⟶ projModelCR W₃.toProjective)
    (hg : g ≫ projModelStrCR W₃.toProjective = projModelStrCR W₁.toProjective)
    (hfhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t (projModelStrCR W₁.toProjective)),
      (⟨((𝒢 T W₁ hΔ₁).mul t x y).1 ≫ f, by rw [Category.assoc, hf]; exact ((𝒢 T W₁ hΔ₁).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR W₂.toProjective)) =
        (𝒢 T W₂ hΔ₂).mul t ⟨x.1 ≫ f, by rw [Category.assoc, hf]; exact x.2⟩ ⟨y.1 ≫ f, by rw [Category.assoc, hf]; exact y.2⟩)
    (hghom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t (projModelStrCR W₁.toProjective)),
      (⟨((𝒢 T W₁ hΔ₁).mul t x y).1 ≫ g, by rw [Category.assoc, hg]; exact ((𝒢 T W₁ hΔ₁).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR W₃.toProjective)) =
        (𝒢 T W₃ hΔ₃).mul t ⟨x.1 ≫ g, by rw [Category.assoc, hg]; exact x.2⟩ ⟨y.1 ≫ g, by rw [Category.assoc, hg]; exact y.2⟩)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] [Surjective g]
    (m : ℕ) (hfrk : ∀ p, f.finrank p = m) (hgrk : ∀ p, g.finrank p = m)
    (K : Scheme) (ι : K ⟶ projModelCR W₁.toProjective) [IsClosedImmersion ι]
    [Flat (ι ≫ projModelStrCR W₁.toProjective)] [LocallyOfFinitePresentation (ι ≫ projModelStrCR W₁.toProjective)]
    (hKrk : ∀ s, (ι ≫ projModelStrCR W₁.toProjective).finrank s = m)
    (hKf : ι ≫ f = (ι ≫ projModelStrCR W₁.toProjective) ≫ ((𝒢 T W₂ hΔ₂).one (𝟙 _)).1)
    (hKg : ι ≫ g = (ι ≫ projModelStrCR W₁.toProjective) ≫ ((𝒢 T W₃ hΔ₃).one (𝟙 _)).1)
    {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x : SchemeHomOver t (projModelStrCR W₁.toProjective)) :
    (⟨x.1 ≫ f, by rw [Category.assoc, hf]; exact x.2⟩ : SchemeHomOver t (projModelStrCR W₂.toProjective)) = (𝒢 T W₂ hΔ₂).one t ↔
      (⟨x.1 ≫ g, by rw [Category.assoc, hg]; exact x.2⟩ : SchemeHomOver t (projModelStrCR W₃.toProjective)) = (𝒢 T W₃ hΔ₃).one t := by
  have h₁ := comp_eq_one_iff_exists_fac (𝒢 T W₁ hΔ₁) (𝒢 T W₂ hΔ₂) f hf hfhom m hfrk K ι hKrk hKf t x
  have h₂ := comp_eq_one_iff_exists_fac (𝒢 T W₁ hΔ₁) (𝒢 T W₃ hΔ₃) g hg hghom m hgrk K ι hKrk hKg t x
  exact h₁.trans h₂.symm

end S_WeierstrassCurve_DrinfeldGlobal_comp_eq_one_iff_comp_eq_one_of_finrank_eq_of_isClosedImmersion
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_comp_eq_one_iff_comp_eq_one_of_finrank_eq_of_isClosedImmersion (solution)
