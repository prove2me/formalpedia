-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.existsUnique_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3cd8188e-5158-5be5-a902-c31ef0502a3c

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_forall_ker_of_flat_of_surjective
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_goodReductionJacobian_mul_eq_and_nsmul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_existsUnique_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

open GoodReductionJacobian in

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
    [IsFinite f] [Flat f] [Surjective f]
    (hker : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x : SchemeHomOver t (projModelStrCR W₁.toProjective)),
      (⟨x.1 ≫ f, by rw [Category.assoc, hf]; exact x.2⟩ : SchemeHomOver t (projModelStrCR W₂.toProjective)) = (𝒢 T W₂ hΔ₂).one t →
      (⟨x.1 ≫ g, by rw [Category.assoc, hg]; exact x.2⟩ : SchemeHomOver t (projModelStrCR W₃.toProjective)) = (𝒢 T W₃ hΔ₃).one t) :
    ∃! h : projModelCR W₂.toProjective ⟶ projModelCR W₃.toProjective, f ≫ h = g := by
  obtain ⟨G₁, hmul₁, hone₁, -, -⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_goodReductionJacobian_mul_eq_and_nsmul_eq (𝒢 T W₁ hΔ₁)
  obtain ⟨G₂, hmul₂, hone₂, -, -⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_goodReductionJacobian_mul_eq_and_nsmul_eq (𝒢 T W₂ hΔ₂)
  obtain ⟨G₃, hmul₃, hone₃, -, -⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_goodReductionJacobian_mul_eq_and_nsmul_eq (𝒢 T W₃ hΔ₃)
  haveI : QuasiCompact f := inferInstance
  obtain ⟨h, hfh, -, huniq⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.existsUnique_comp_eq_of_forall_ker_of_flat_of_surjective
      G₁ G₂ G₃ f hf
      (fun t P Q => by
        apply Subtype.ext
        show (G₁.mul t P Q).1 ≫ f = (G₂.mul t _ _).1
        rw [hmul₁, hmul₂]
        exact congrArg Subtype.val (hfhom t P Q))
      g hg
      (fun t P Q => by
        apply Subtype.ext
        show (G₁.mul t P Q).1 ≫ g = (G₃.mul t _ _).1
        rw [hmul₁, hmul₃]
        exact congrArg Subtype.val (hghom t P Q))
      (fun t P hP => by
        rw [hone₂] at hP
        rw [hone₃]
        exact hker t P hP)
  exact ⟨h, hfh, fun h' hh' => huniq h' hh'⟩

end S_WeierstrassCurve_DrinfeldGlobal_existsUnique_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_existsUnique_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one (solution)
