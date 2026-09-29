-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.isLevel_map_of_comp_projMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e8853f56-bb1a-5640-b27b-8798c05d43fb

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_one_comp_projMap_eq_of_isOriginChartSection
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comap_torsionIdealOver_eq_torsionIdeal
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comap_basisDivisorOver_eq_basisDivisor
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_basisDivisorOver_comap_mapOnProdOver
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_iff_isDrinfeldBasisOver_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_isLevel_map_of_comp_projMap_eq

set_option autoImplicit false

universe u

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal P2MW.S_WeierstrassCurve_DrinfeldGlobal_isLevel_map_of_comp_projMap_eq.WeierstrassCurve.DrinfeldGlobal"

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map map_Δ Δ DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom DrinfeldGlobal.comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection DrinfeldGlobal.comap_torsionIdealOver_eq_torsionIdeal DrinfeldGlobal.comap_basisDivisorOver_eq_basisDivisor DrinfeldGlobal.isDrinfeldBasis_iff_isDrinfeldBasisOver_id"
namespace DrinfeldGlobal
p2m_export "WeierstrassCurve.DrinfeldGlobal" "GroupLaws RawDrinfeldPair.IsLevel base IsDrinfeldBasis RawDrinfeldPair IsCoefficientHom isPullback_projMap_of_isCoefficientHom comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq one_comp_projMap_eq_of_isOriginChartSection comap_torsionIdealOver_eq_torsionIdeal comap_basisDivisorOver_eq_basisDivisor isDrinfeldBasis_iff_isDrinfeldBasisOver_id"
namespace LevelMap
p2m_open "WeierstrassCurve.DrinfeldGlobal WeierstrassCurve"

theorem comap_injective_of_isIso {X Y : Scheme.{u}} (θ : X ⟶ Y) [IsIso θ] {I J : Y.IdealSheafData}
    (h : I.comap θ = J.comap θ) : I = J := by
  have : ∀ K : Y.IdealSheafData, K = (K.comap θ).comap (inv θ) := fun K ↦ by
    rw [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  rw [this I, this J, h]

end WeierstrassCurve.DrinfeldGlobal.LevelMap

open WeierstrassCurve.DrinfeldGlobal.LevelMap in
set_option maxHeartbeats 3200000 in
theorem solution
    {A : Type u} [CommRing A] (q : ℕ) (𝒢 : GroupLaws A) (h𝒢O : 𝒢.IsOriginIdentity)
    {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (W : WeierstrassCurve T) (x : RawDrinfeldPair T) (y : RawDrinfeldPair T')
    (hy : y.curve = x.curve.map f.toRingHom)
    (hpin : ∀ (φ : projModelGradingCR x.curve →+*ᵍ projModelGradingCR (x.curve.map f.toRingHom))
      (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (x.curve.map f.toRingHom)) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR x.curve)).map φ),
      IsCoefficientHom x.curve f.toRingHom φ →
        y.P.1 ≫ eqToHom (congrArg projModelCR hy) ≫ Proj.map φ hφ =
          Spec.map (CommRingCat.ofHom f.toRingHom) ≫ x.P.1 ∧
        y.Q.1 ≫ eqToHom (congrArg projModelCR hy) ≫ Proj.map φ hφ =
          Spec.map (CommRingCat.ofHom f.toRingHom) ≫ x.Q.1) :
    RawDrinfeldPair.IsLevel 𝒢 q W x → RawDrinfeldPair.IsLevel 𝒢 q (W.map f.toRingHom) y := by
  obtain ⟨xc, xP, xQ⟩ := x
  obtain ⟨yc, yP, yQ⟩ := y
  change yc = xc.map f.toRingHom at hy
  subst hy
  rintro ⟨hxW, hΔ, hlev⟩
  change xc = W at hxW
  subst hxW
  change IsUnit xc.Δ at hΔ
  refine ⟨rfl, ?_⟩
  have hΔ' : IsUnit (WeierstrassCurve.map xc f.toRingHom).Δ := by
    rw [WeierstrassCurve.map_Δ]; exact hΔ.map _
  refine ⟨hΔ', ?_⟩
  haveI : WeierstrassCurve.IsElliptic xc := ⟨hΔ⟩
  set G : RelativeGroupLaw T (projModelStrCR xc) := 𝒢 T xc hΔ with hG
  set L : RelativeGroupLaw T' (projModelStrCR (xc.map f.toRingHom)) := 𝒢 T' (xc.map f.toRingHom) hΔ' with hL
  change IsDrinfeldBasis L q yP yQ
  change IsDrinfeldBasis G q xP xQ at hlev

  obtain ⟨φc, hφc, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom xc f.toRingHom
  have hK2 := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom xc f.toRingHom φc hφc hcoef
  have hsq : Proj.map φc hφc ≫ projModelStrCR xc =
      projModelStrCR (xc.map f.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) := hK2.w

  obtain ⟨χ, hχ, hχx, hχz⟩ := h𝒢O T xc hΔ
  obtain ⟨χ', hχ', hχ'x, hχ'z⟩ := h𝒢O T' (xc.map f.toRingHom) hΔ'
  have hone := WeierstrassCurve.DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection xc f.toRingHom φc hφc hcoef
    G L χ (hG ▸ hχ) hχx hχz χ' (hL ▸ hχ') hχ'x hχ'z
  have hmul : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T'))
      (a b : SchemeHomOver s (projModelStrCR (xc.map f.toRingHom))),
      (L.mul s a b).1 ≫ Proj.map φc hφc =
        (G.mul (s ≫ Spec.map (CommRingCat.ofHom f.toRingHom))
          ⟨a.1 ≫ Proj.map φc hφc, by rw [Category.assoc, hsq, ← Category.assoc, a.2]⟩
          ⟨b.1 ≫ Proj.map φc hφc, by rw [Category.assoc, hsq, ← Category.assoc, b.2]⟩).1 :=
    fun s a b ↦ WeierstrassCurve.DrinfeldGlobal.comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq xc f.toRingHom
      φc hφc hcoef G L hone hsq s a b

  have hT := WeierstrassCurve.DrinfeldGlobal.comap_torsionIdealOver_eq_torsionIdeal xc f.toRingHom φc hφc hcoef hsq G L
    hmul hone q
  have hD := WeierstrassCurve.DrinfeldGlobal.comap_basisDivisorOver_eq_basisDivisor xc f.toRingHom φc hφc hcoef hsq G L
    hmul hone q yP yQ
  set Θ := pullback.lift (pullback.fst (projModelStrCR (xc.map f.toRingHom)) (𝟙 _) ≫ Proj.map φc hφc)
        (pullback.snd (projModelStrCR (xc.map f.toRingHom)) (𝟙 _))
        (by rw [Category.assoc, hsq, ← Category.assoc, pullback.condition, Category.assoc, Category.id_comp]) with hΘ
  have hΘeq : Θ = pullback.fst (projModelStrCR (xc.map f.toRingHom)) (𝟙 _) ≫ hK2.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [hΘ, pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst]
    · rw [hΘ, pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, pullback.condition,
        Category.comp_id]
  haveI : IsIso Θ := by rw [hΘeq]; infer_instance

  obtain ⟨hPπ, hQπ⟩ := hpin φc hφc hcoef
  simp only [eqToHom_refl, Category.id_comp] at hPπ hQπ

  have hOver : G.IsDrinfeldBasisOver q (Spec.map (CommRingCat.ofHom f.toRingHom))
      ⟨yP.1 ≫ Proj.map φc hφc, by rw [Category.assoc, hsq, ← Category.assoc, yP.2, Category.id_comp]⟩
      ⟨yQ.1 ≫ Proj.map φc hφc, by rw [Category.assoc, hsq, ← Category.assoc, yQ.2, Category.id_comp]⟩ := by
    have h1 : G.IsDrinfeldBasisOver q (𝟙 _) xP xQ :=
      (WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_iff_isDrinfeldBasisOver_id G q xP xQ).mp hlev
    have h7 := WeierstrassProjModel.RelativeGroupLaw.basisDivisorOver_comap_mapOnProdOver G q
      (t := 𝟙 (Spec (CommRingCat.of T))) (t' := Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom)) (Category.comp_id _) xP xQ
    have h2 : G.IsDrinfeldBasisOver q (Spec.map (CommRingCat.ofHom f.toRingHom))
        (schemeHomOverComp (Spec.map (CommRingCat.ofHom f.toRingHom)) (Category.comp_id _) xP)
        (schemeHomOverComp (Spec.map (CommRingCat.ofHom f.toRingHom)) (Category.comp_id _) xQ) := by
      unfold WeierstrassProjModel.RelativeGroupLaw.IsDrinfeldBasisOver at h1 ⊢
      rw [← h7.1, ← h7.2, h1]
    convert h2 using 2
    all_goals first | rfl | exact hPπ | exact hQπ

  unfold IsDrinfeldBasis
  unfold WeierstrassProjModel.RelativeGroupLaw.IsDrinfeldBasisOver at hOver
  rw [← hT, ← hD]
  exact congrArg (fun I ↦ Scheme.IdealSheafData.comap I Θ) hOver

end S_WeierstrassCurve_DrinfeldGlobal_isLevel_map_of_comp_projMap_eq
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_isLevel_map_of_comp_projMap_eq (solution)
