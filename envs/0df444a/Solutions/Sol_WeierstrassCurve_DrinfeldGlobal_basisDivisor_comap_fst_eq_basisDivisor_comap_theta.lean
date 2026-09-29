-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.basisDivisor_comap_fst_eq_basisDivisor_comap_theta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/fad1cf16-a278-55d0-8bab-31b3025c5a42

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comp_projMap_eq_at_field_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_one_comp_projMap_eq_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_fst_eq_prodKerGraph_comap_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_basisDivisor_comap_fst_eq_basisDivisor_comap_theta
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

namespace P2Aux
open WeierstrassProjModel NeronModelInfra

variable {B T X : Scheme.{u}}

theorem mul_val_congr {R : Type u} [CommRing R] {f : X ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) (x y : SchemeHomOver t₁ f) :
    (G.mul t₂ ⟨x.1, h ▸ x.2⟩ ⟨y.1, h ▸ y.2⟩).1 = (G.mul t₁ x y).1 := by
  subst h; rfl

theorem one_val_congr {R : Type u} [CommRing R] {f : X ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) :
    (G.one t₂).1 = (G.one t₁).1 := by
  subst h; rfl

end P2Aux

theorem solution
    (A : Type u) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type u) [CommRing T] [Algebra A T] (K : Type u) [Field K] [Algebra A K] (ι : T →ₐ[A] K)
    (W₀ : WeierstrassCurve T) (hΔ₀ : IsUnit W₀.Δ) (hΔ' : IsUnit (W₀.map ι.toRingHom).Δ) (n : ℕ)
    (φ : projModelGradingCR W₀ →+*ᵍ projModelGradingCR (W₀.map ι.toRingHom))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W₀.map ι.toRingHom)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W₀)).map φ)
    (hφc : IsCoefficientHom W₀ ι.toRingHom φ)
    (P₀ Q₀ : Section W₀) (P' Q' : Section (W₀.map ι.toRingHom))
    (hP : P'.1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ P₀.1)
    (hQ : Q'.1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ Q₀.1)
    (θ : pullback (pullback.snd (projModelStrCR W₀) (𝟙 (Spec (CommRingCat.of T))))
          (Spec.map (CommRingCat.ofHom ι.toRingHom)) ⟶
        pullback (projModelStrCR (W₀.map ι.toRingHom)) (𝟙 (Spec (CommRingCat.of K))))
    (hθ₁ : θ ≫ pullback.fst _ _ ≫ Proj.map φ hφ =
      pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom)) ≫
        pullback.fst _ _)
    (hθ₂ : θ ≫ pullback.snd _ _ =
      pullback.snd (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom))) :
    (basisDivisor (𝒢 T W₀ hΔ₀) n P₀ Q₀).comap
        (pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom))) =
      (basisDivisor (𝒢 K (W₀.map ι.toRingHom) hΔ') n P' Q').comap θ := by
  haveI : (W₀.map ι.toRingHom).toAffine.IsElliptic := ⟨hΔ'⟩
  haveI : W₀.toAffine.IsElliptic := ⟨hΔ₀⟩
  have H := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W₀ ι.toRingHom φ hφ hφc

  have hsq : Proj.map φ hφ ≫ projModelStrCR W₀ =
      projModelStrCR (W₀.map ι.toRingHom) ≫ Spec.map (CommRingCat.ofHom ι.toRingHom) := H.w

  have hone : ((𝒢 K (W₀.map ι.toRingHom) hΔ').one (𝟙 _)).1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ ((𝒢 T W₀ hΔ₀).one (𝟙 _)).1 := by
    have h1 := WeierstrassCurve.DrinfeldGlobal.GroupLaws.one_comp_projMap_eq_of_isCoefficientHom A 𝒢 h𝒢O T K ι W₀ hΔ₀ hΔ'
      φ hφ hφc (𝟙 (Spec (CommRingCat.of K)))
    rw [h1]
    have hψ : Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ 𝟙 (Spec (CommRingCat.of T)) =
        𝟙 (Spec (CommRingCat.of K)) ≫ Spec.map (CommRingCat.ofHom ι.toRingHom) := by simp
    have := (𝒢 T W₀ hΔ₀).one_natural (𝟙 _) (𝟙 _ ≫ Spec.map (CommRingCat.ofHom ι.toRingHom))
      (Spec.map (CommRingCat.ofHom ι.toRingHom)) hψ
    rw [← this, WeierstrassProjModel.schemeHomOverComp_coe]
  have hmul : ∀ (x' y' : Section (W₀.map ι.toRingHom)) (x y : Section W₀),
      x'.1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ x.1 →
      y'.1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ y.1 →
      ((𝒢 K (W₀.map ι.toRingHom) hΔ').mul (𝟙 _) x' y').1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ ((𝒢 T W₀ hΔ₀).mul (𝟙 _) x y).1 := by
    intro x' y' x y hx hy
    have hK : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (CommRingCat.of K)) := by
      simp [Algebra.algebraMap_self]

    have e1 := (P2Aux.mul_val_congr (𝒢 K (W₀.map ι.toRingHom) hΔ') hK.symm x' y').symm

    have hc := WeierstrassCurve.DrinfeldGlobal.GroupLaws.mul_comp_projMap_eq_at_field_of_isCoefficientHom A 𝒢 h𝒢 h𝒢O T K ι
      W₀ hΔ₀ hΔ' φ hφ hφc K ⟨x'.1, hK.symm ▸ x'.2⟩ ⟨y'.1, hK.symm ▸ y'.2⟩
      ⟨x'.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, x'.2, hK]⟩
      ⟨y'.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, y'.2, hK]⟩ rfl rfl
    rw [e1, hc]

    have hidx : Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ 𝟙 (Spec (CommRingCat.of T)) =
        Spec.map (CommRingCat.ofHom (algebraMap K K)) ≫ Spec.map (CommRingCat.ofHom ι.toRingHom) := by
      rw [hK]; simp
    have hn := (𝒢 T W₀ hΔ₀).mul_natural (𝟙 _) _ (Spec.map (CommRingCat.ofHom ι.toRingHom)) hidx x y
    have ex : (⟨x'.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, x'.2, hK]⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K)) ≫ Spec.map (CommRingCat.ofHom ι.toRingHom)) (projModelStrCR W₀)) =
        WeierstrassProjModel.schemeHomOverComp (Spec.map (CommRingCat.ofHom ι.toRingHom)) hidx x :=
      Subtype.ext (by rw [WeierstrassProjModel.schemeHomOverComp_coe]; exact hx)
    have ey : (⟨y'.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, y'.2, hK]⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K)) ≫ Spec.map (CommRingCat.ofHom ι.toRingHom)) (projModelStrCR W₀)) =
        WeierstrassProjModel.schemeHomOverComp (Spec.map (CommRingCat.ofHom ι.toRingHom)) hidx y :=
      Subtype.ext (by rw [WeierstrassProjModel.schemeHomOverComp_coe]; exact hy)
    rw [ex, ey, ← hn, WeierstrassProjModel.schemeHomOverComp_coe]
  have hnsmul : ∀ (m : ℕ) (x' : Section (W₀.map ι.toRingHom)) (x : Section W₀),
      x'.1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ x.1 →
      ((𝒢 K (W₀.map ι.toRingHom) hΔ').nsmul (𝟙 _) m x').1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ ((𝒢 T W₀ hΔ₀).nsmul (𝟙 _) m x).1 := by
    intro m x' x hx
    induction m with
    | zero => simpa [RelativeGroupLaw.nsmul] using hone
    | succ m ih => exact hmul _ _ _ _ ih hx
  have hlin : ∀ a b : ℕ, (linComb (𝒢 K (W₀.map ι.toRingHom) hΔ') P' Q' a b).1 ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ (linComb (𝒢 T W₀ hΔ₀) P₀ Q₀ a b).1 :=
    fun a b => hmul _ _ _ _ (hnsmul a P' P₀ hP) (hnsmul b Q' Q₀ hQ)

  exact AlgebraicGeometry.prodKerGraph_comap_fst_eq_prodKerGraph_comap_of_isPullback
    (projModelStrCR W₀) (projModelStrCR (W₀.map ι.toRingHom)) (Spec.map (CommRingCat.ofHom ι.toRingHom)) (Proj.map φ hφ) H
    (basisTuple (𝒢 T W₀ hΔ₀) n P₀ Q₀) (basisTuple_over (𝒢 T W₀ hΔ₀) n P₀ Q₀) (basisTuple (𝒢 K (W₀.map ι.toRingHom) hΔ') n P' Q') (basisTuple_over (𝒢 K (W₀.map ι.toRingHom) hΔ') n P' Q')
    (fun i => hlin _ _) θ hθ₁ hθ₂

end S_WeierstrassCurve_DrinfeldGlobal_basisDivisor_comap_fst_eq_basisDivisor_comap_theta
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_basisDivisor_comap_fst_eq_basisDivisor_comap_theta (solution)
