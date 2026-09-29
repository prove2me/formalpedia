-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.isLevel_iff_isDrinfeldBasisOver_comp_projMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2e4a81d8-5a3f-5930-ab07-8daeb4b21b68

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_one_comp_projMap_eq_of_isOriginChartSection
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comap_torsionIdealOver_eq_torsionIdeal
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comap_basisDivisorOver_eq_basisDivisor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_isLevel_iff_isDrinfeldBasisOver_comp_projMap
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

universe u

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal P2MW.S_WeierstrassCurve_DrinfeldGlobal_isLevel_iff_isDrinfeldBasisOver_comp_projMap.WeierstrassCurve.DrinfeldGlobal"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map map_Δ Δ Projective DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom DrinfeldGlobal.comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection DrinfeldGlobal.comap_torsionIdealOver_eq_torsionIdeal DrinfeldGlobal.comap_basisDivisorOver_eq_basisDivisor"
namespace DrinfeldGlobal
p2m_export "WeierstrassCurve.DrinfeldGlobal" "GroupLaws RawDrinfeldPair.IsLevel IsDrinfeldBasis RawDrinfeldPair IsCoefficientHom isPullback_projMap_of_isCoefficientHom comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq one_comp_projMap_eq_of_isOriginChartSection comap_torsionIdealOver_eq_torsionIdeal comap_basisDivisorOver_eq_basisDivisor"
namespace LevelDict
p2m_open "WeierstrassCurve.DrinfeldGlobal WeierstrassCurve"

theorem comap_injective_of_isIso {X Y : Scheme.{u}} (θ : X ⟶ Y) [IsIso θ] {I J : Y.IdealSheafData}
    (h : I.comap θ = J.comap θ) : I = J := by
  have : ∀ K : Y.IdealSheafData, K = (K.comap θ).comap (inv θ) := fun K ↦ by
    rw [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  rw [this I, this J, h]

end WeierstrassCurve.DrinfeldGlobal.LevelDict

open WeierstrassCurve.DrinfeldGlobal.LevelDict in
set_option maxHeartbeats 3200000 in
theorem solution
    {A : Type u} [CommRing A] (q : ℕ) [Fact q.Prime]
    (𝒢 : GroupLaws A) (h𝒢O : 𝒢.IsOriginIdentity)
    (B : Type u) [CommRing B] [Algebra A B] (W : WeierstrassCurve.Projective B) (hΔ : IsUnit W.Δ)
    (T : Type u) [CommRing T] [Algebra A T] (φ : B →ₐ[A] T)
    (φc : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map φ.toRingHom))
    (hφc : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map φ.toRingHom)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φc)
    (hcoef : IsCoefficientHom W φ.toRingHom φc)
    (hsq : Proj.map φc hφc ≫ projModelStrCR W =
      projModelStrCR (W.map φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (x : RawDrinfeldPair T) (hc : x.curve = W.map φ.toRingHom)
    (hP : (x.P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φc hφc) ≫ projModelStrCR W =
      Spec.map (CommRingCat.ofHom φ.toRingHom))
    (hQ : (x.Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φc hφc) ≫ projModelStrCR W =
      Spec.map (CommRingCat.ofHom φ.toRingHom)) :
    RawDrinfeldPair.IsLevel 𝒢 q (W.map φ.toRingHom) x ↔
      (𝒢 B W hΔ).IsDrinfeldBasisOver q (Spec.map (CommRingCat.ofHom φ.toRingHom))
        ⟨x.P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φc hφc, hP⟩
        ⟨x.Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φc hφc, hQ⟩ := by
  obtain ⟨xc, xP, xQ⟩ := x
  cases hc

  have hΔ' : IsUnit (WeierstrassCurve.map W φ.toRingHom).Δ := by
    rw [WeierstrassCurve.map_Δ]; exact hΔ.map _
  haveI : WeierstrassCurve.IsElliptic W := ⟨hΔ⟩
  set G : RelativeGroupLaw B (projModelStrCR W) := 𝒢 B W hΔ with hG
  set L : RelativeGroupLaw T (projModelStrCR (W.map φ.toRingHom)) := 𝒢 T (W.map φ.toRingHom) hΔ' with hL

  obtain ⟨χ, hχ, hχx, hχz⟩ := h𝒢O B W hΔ
  obtain ⟨χ', hχ', hχ'x, hχ'z⟩ := h𝒢O T (W.map φ.toRingHom) hΔ'
  have hone := WeierstrassCurve.DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection W φ.toRingHom φc hφc hcoef
    G L χ (hG ▸ hχ) hχx hχz χ' (hL ▸ hχ') hχ'x hχ'z
  have hmul : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T))
      (x y : SchemeHomOver s (projModelStrCR (W.map φ.toRingHom))),
      (L.mul s x y).1 ≫ Proj.map φc hφc =
        (G.mul (s ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
          ⟨x.1 ≫ Proj.map φc hφc, by rw [Category.assoc, hsq, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ Proj.map φc hφc, by rw [Category.assoc, hsq, ← Category.assoc, y.2]⟩).1 :=
    fun s x y ↦ WeierstrassCurve.DrinfeldGlobal.comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq W φ.toRingHom
      φc hφc hcoef G L hone hsq s x y

  have hT := WeierstrassCurve.DrinfeldGlobal.comap_torsionIdealOver_eq_torsionIdeal W φ.toRingHom φc hφc hcoef hsq G L
    hmul hone q
  have hD := WeierstrassCurve.DrinfeldGlobal.comap_basisDivisorOver_eq_basisDivisor W φ.toRingHom φc hφc hcoef hsq G L
    hmul hone q xP xQ

  have hK2 := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W φ.toRingHom φc hφc hcoef
  set Θ := pullback.lift (pullback.fst (projModelStrCR (W.map φ.toRingHom)) (𝟙 _) ≫ Proj.map φc hφc)
        (pullback.snd (projModelStrCR (W.map φ.toRingHom)) (𝟙 _))
        (by rw [Category.assoc, hsq, ← Category.assoc, pullback.condition, Category.assoc, Category.id_comp]) with hΘ
  have hΘeq : Θ = pullback.fst (projModelStrCR (W.map φ.toRingHom)) (𝟙 _) ≫ hK2.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [hΘ, pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst]
    · rw [hΘ, pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, pullback.condition,
        Category.comp_id]
  haveI : IsIso Θ := by rw [hΘeq]; infer_instance

  have key : IsDrinfeldBasis L q xP xQ ↔
      G.IsDrinfeldBasisOver q (Spec.map (CommRingCat.ofHom φ.toRingHom))
        ⟨xP.1 ≫ Proj.map φc hφc, by (first | exact hP | simpa [Category.assoc] using hP | (have h__ := hP; simp [Category.assoc] at h__; exact h__))⟩
        ⟨xQ.1 ≫ Proj.map φc hφc, by (first | exact hQ | simpa [Category.assoc] using hQ | (have h__ := hQ; simp [Category.assoc] at h__; exact h__))⟩ := by
    unfold IsDrinfeldBasis WeierstrassProjModel.RelativeGroupLaw.IsDrinfeldBasisOver
    rw [← hT, ← hD]
    exact ⟨fun h ↦ comap_injective_of_isIso Θ h, fun h ↦ congrArg (fun I ↦ Scheme.IdealSheafData.comap I Θ) h⟩
  constructor
  · rintro ⟨-, hΔ'', hlev⟩
    have : G.IsDrinfeldBasisOver q (Spec.map (CommRingCat.ofHom φ.toRingHom)) _ _ := key.mp hlev
    convert this using 2 <;> first | rfl | exact Subsingleton.elim _ _
  · intro h
    refine ⟨rfl, hΔ', key.mpr ?_⟩
    convert h using 2 <;> first | rfl | exact Subsingleton.elim _ _

end S_WeierstrassCurve_DrinfeldGlobal_isLevel_iff_isDrinfeldBasisOver_comp_projMap
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_isLevel_iff_isDrinfeldBasisOver_comp_projMap (solution)
