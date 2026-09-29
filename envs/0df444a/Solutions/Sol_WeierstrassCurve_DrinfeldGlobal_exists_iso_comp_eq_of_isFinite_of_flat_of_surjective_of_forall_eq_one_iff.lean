-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_iso_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4b996406-2556-5dfd-b35d-940e7c5d57e0

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_existsUnique_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_iso_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one_iff
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing FormalGroup
attribute [local instance] MvPolynomial.gradedAlgebra

namespace IsoCommonKernelAux

theorem one_comp_eq_one {T : Type} [CommRing T] {X₁ X₂ : Scheme}
    {p₁ : X₁ ⟶ Spec (CommRingCat.of T)} {p₂ : X₂ ⟶ Spec (CommRingCat.of T)}
    (G₁ : RelativeGroupLaw T p₁) (G₂ : RelativeGroupLaw T p₂) (f : X₁ ⟶ X₂) (hf : f ≫ p₂ = p₁)
    (hfhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t p₁),
      (⟨(G₁.mul t x y).1 ≫ f, by rw [Category.assoc, hf]; exact (G₁.mul t x y).2⟩ : SchemeHomOver t p₂) =
        G₂.mul t ⟨x.1 ≫ f, by rw [Category.assoc, hf]; exact x.2⟩ ⟨y.1 ≫ f, by rw [Category.assoc, hf]; exact y.2⟩)
    {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) :
    (G₁.one t).1 ≫ f = (G₂.one t).1 := by
  letI : Group (SchemeHomOver t p₂) := G₂.pointGroup t
  let a : SchemeHomOver t p₂ := ⟨(G₁.one t).1 ≫ f, by rw [Category.assoc, hf]; exact (G₁.one t).2⟩
  have h1 : (G₁.one t).1 ≫ f = (G₂.mul t a a).1 := by
    have h := congrArg Subtype.val (hfhom t (G₁.one t) (G₁.one t))
    rw [G₁.one_mul] at h
    exact h
  have h2 : a = a * a := Subtype.ext h1
  have h3 : a = 1 := by
    have h4 : a * 1 = a * a := by rw [mul_one]; exact h2
    exact (mul_left_cancel h4).symm
  exact congrArg Subtype.val h3

end IsoCommonKernelAux

open IsoCommonKernelAux

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
    (hker : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x : SchemeHomOver t (projModelStrCR W₁.toProjective)),
      (⟨x.1 ≫ f, by rw [Category.assoc, hf]; exact x.2⟩ : SchemeHomOver t (projModelStrCR W₂.toProjective)) = (𝒢 T W₂ hΔ₂).one t ↔
      (⟨x.1 ≫ g, by rw [Category.assoc, hg]; exact x.2⟩ : SchemeHomOver t (projModelStrCR W₃.toProjective)) = (𝒢 T W₃ hΔ₃).one t) :
    ∃ Ψ : projModelCR W₂.toProjective ≅ projModelCR W₃.toProjective,
      Ψ.hom ≫ projModelStrCR W₃.toProjective = projModelStrCR W₂.toProjective ∧
      f ≫ Ψ.hom = g ∧
      (kwZeroSect T W₂).1 ≫ Ψ.hom = (kwZeroSect T W₃).1 := by
  classical
  obtain ⟨h, hfh, hu⟩ :=
    WeierstrassCurve.DrinfeldGlobal.existsUnique_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one
      A 𝒢 h𝒢 h𝒢O T W₁ W₂ W₃ hΔ₁ hΔ₂ hΔ₃ f hf g hg hfhom hghom (fun t x hx => (hker t x).mp hx)
  obtain ⟨h', hgh', hu'⟩ :=
    WeierstrassCurve.DrinfeldGlobal.existsUnique_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one
      A 𝒢 h𝒢 h𝒢O T W₁ W₃ W₂ hΔ₁ hΔ₃ hΔ₂ g hg f hf hghom hfhom (fun t x hx => (hker t x).mpr hx)
  have hhh' : h ≫ h' = 𝟙 _ := by
    obtain ⟨e, -, hue⟩ :=
      WeierstrassCurve.DrinfeldGlobal.existsUnique_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one
        A 𝒢 h𝒢 h𝒢O T W₁ W₂ W₂ hΔ₁ hΔ₂ hΔ₂ f hf f hf hfhom hfhom (fun t x hx => hx)
    rw [hue (h ≫ h') (show f ≫ (h ≫ h') = f by rw [← Category.assoc, hfh, hgh']),
      ← hue (𝟙 _) (show f ≫ 𝟙 _ = f from Category.comp_id f)]
  have hh'h : h' ≫ h = 𝟙 _ := by
    obtain ⟨e, -, hue⟩ :=
      WeierstrassCurve.DrinfeldGlobal.existsUnique_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one
        A 𝒢 h𝒢 h𝒢O T W₁ W₃ W₃ hΔ₁ hΔ₃ hΔ₃ g hg g hg hghom hghom (fun t x hx => hx)
    rw [hue (h' ≫ h) (show g ≫ (h' ≫ h) = g by rw [← Category.assoc, hgh', hfh]),
      ← hue (𝟙 _) (show g ≫ 𝟙 _ = g from Category.comp_id g)]
  refine ⟨⟨h, h', hhh', hh'h⟩, ?_, hfh, ?_⟩
  · haveI : Epi f := inferInstance
    rw [← cancel_epi f, ← Category.assoc, hfh, hg, hf]
  · have hone₁ := (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W₁
      (𝒢 T W₁ hΔ₁)).mp (h𝒢O T W₁.toProjective hΔ₁)
    have hone₂ := (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W₂
      (𝒢 T W₂ hΔ₂)).mp (h𝒢O T W₂.toProjective hΔ₂)
    have hone₃ := (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W₃
      (𝒢 T W₃ hΔ₃)).mp (h𝒢O T W₃.toProjective hΔ₃)
    have e1 := one_comp_eq_one (𝒢 T W₁ hΔ₁) (𝒢 T W₂ hΔ₂) f hf hfhom (𝟙 _)
    have e2 := one_comp_eq_one (𝒢 T W₁ hΔ₁) (𝒢 T W₃ hΔ₃) g hg hghom (𝟙 _)
    show (kwZeroSect T W₂).1 ≫ h = (kwZeroSect T W₃).1
    rw [← hone₂, ← e1, Category.assoc, hfh, e2, hone₃]

end S_WeierstrassCurve_DrinfeldGlobal_exists_iso_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one_iff
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_iso_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one_iff (solution)
