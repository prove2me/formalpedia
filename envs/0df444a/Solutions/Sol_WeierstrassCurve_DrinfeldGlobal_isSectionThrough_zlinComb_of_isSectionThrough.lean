-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.isSectionThrough_zlinComb_of_isSectionThrough
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fe03eea5-6f66-5d76-8698-ffe05ec48518

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_zlinComb_of_isSectionThrough
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X"

set_option autoImplicit false
set_option linter.unusedVariables false

open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve.LevelRelabelling

open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

theorem solution
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    {T : Type} [Field T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (S S' : Section W) (x y x' y' : T)
    (hS : IsSectionThrough S x y) (hS' : IsSectionThrough S' x' y') (a b : ℤ) :
    (a • toPoint W x y + b • toPoint W x' y' = 0 →
        zlinComb (𝒢 T W hΔ) S S' a b = (𝒢 T W hΔ).one (𝟙 _)) ∧
    (∀ (xr yr : T) (hr : W.toAffine.Nonsingular xr yr),
        a • toPoint W x y + b • toPoint W x' y' = WeierstrassCurve.Affine.Point.some xr yr hr →
        IsSectionThrough (zlinComb (𝒢 T W hΔ) S S' a b) xr yr) := by
  classical
  haveI : W.toAffine.IsElliptic := ⟨hΔ⟩

  have hG1 : ((𝒢 T W hΔ).one (𝟙 _)).1 = (kwZeroSect T W).1 :=
    (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W (𝒢 T W hΔ)).mp
      (h𝒢O T W hΔ)
  obtain ⟨ev, hev, -, hcoord⟩ :=
    WeierstrassProjModel.exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain W (𝒢 T W hΔ) hG1

  set ι : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of T) := Spec.map (CommRingCat.ofHom (algebraMap T T)) with hι
  have hι1 : ι = 𝟙 _ := by rw [hι, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hψ : ι ≫ 𝟙 (Spec (CommRingCat.of T)) = ι := Category.comp_id _

  have hmul : ∀ P Q : Section W,
      ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).mul _ P Q)) =
        ev T (schemeHomOverComp ι hψ P) + ev T (schemeHomOverComp ι hψ Q) := by
    intro P Q
    rw [(𝒢 T W hΔ).mul_natural (𝟙 _) ι ι hψ P Q]
    exact hev.1 T _ _
  have hone : ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).one _)) = 0 := by
    have h := hmul ((𝒢 T W hΔ).one _) ((𝒢 T W hΔ).one _)
    rw [(𝒢 T W hΔ).one_mul] at h
    have h2 : ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).one _)) + ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).one _)) =
        ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).one _)) + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  have hnsmul : ∀ (k : ℕ) (P : Section W),
      ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).nsmul _ k P)) = k • ev T (schemeHomOverComp ι hψ P) := by
    intro k P
    induction k with
    | zero => rw [RelativeGroupLaw.nsmul_zero, zero_smul]; exact hone
    | succ k ih => rw [RelativeGroupLaw.nsmul_succ, hmul, ih, add_smul, one_smul]
  have hinv : ∀ P : Section W,
      ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).inv _ P)) = - ev T (schemeHomOverComp ι hψ P) := by
    intro P
    have h := hmul ((𝒢 T W hΔ).inv _ P) P
    rw [(𝒢 T W hΔ).inv_mul_cancel, hone] at h
    exact (neg_eq_of_add_eq_zero_left h.symm).symm
  have hzsmul : ∀ (n : ℤ) (P : Section W),
      ev T (schemeHomOverComp ι hψ (zsmulSection (𝒢 T W hΔ) n P)) = n • ev T (schemeHomOverComp ι hψ P) := by
    intro n P
    cases n with
    | ofNat k =>
      show ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).nsmul _ k P)) = ((k : ℕ) : ℤ) • _
      rw [hnsmul, natCast_zsmul]
    | negSucc k =>
      show ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).inv _ ((𝒢 T W hΔ).nsmul _ (k + 1) P))) = _
      rw [hinv, hnsmul, negSucc_zsmul]
  have hlin : ev T (schemeHomOverComp ι hψ (zlinComb (𝒢 T W hΔ) S S' a b)) =
      a • ev T (schemeHomOverComp ι hψ S) + b • ev T (schemeHomOverComp ι hψ S') := by
    show ev T (schemeHomOverComp ι hψ ((𝒢 T W hΔ).mul _ (zsmulSection (𝒢 T W hΔ) a S) (zsmulSection (𝒢 T W hΔ) b S'))) = _
    rw [hmul, hzsmul, hzsmul]

  have hread : ∀ (P : Section W) (u v : T), IsSectionThrough P u v →
      ∃ h : W.toAffine.Nonsingular u v, ev T (schemeHomOverComp ι hψ P) = WeierstrassCurve.Affine.Point.some u v h := by
    intro P u v hP
    obtain ⟨χ, hχ, hu, hv⟩ := hP
    have hfac : (schemeHomOverComp ι hψ P).1 =
        Spec.map (CommRingCat.ofHom ((algebraMap T T).comp χ)) ≫ zChartι W := by
      rw [schemeHomOverComp_coe, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      show ι ≫ P.1 = ι ≫ _
      rw [hχ]
    obtain ⟨hxy, he⟩ := hcoord T (schemeHomOverComp ι hψ P) ((algebraMap T T).comp χ) hfac
    have hu' : ((algebraMap T T).comp χ) (xOverZ W) = u := by rw [RingHom.comp_apply, Algebra.algebraMap_self_apply]; exact hu
    have hv' : ((algebraMap T T).comp χ) (yOverZ W) = v := by rw [RingHom.comp_apply, Algebra.algebraMap_self_apply]; exact hv
    refine ⟨?_, ?_⟩
    · have h := hxy; rw [hu', hv'] at h; exact h
    · rw [he]
      congr 1

  have hinj : ∀ P Q : Section W, schemeHomOverComp ι hψ P = schemeHomOverComp ι hψ Q → P = Q := by
    intro P Q h
    have h1 := congrArg Subtype.val h
    rw [schemeHomOverComp_coe, schemeHomOverComp_coe, hι1, Category.id_comp, Category.id_comp] at h1
    exact Subtype.ext h1
  obtain ⟨hxy, heS⟩ := hread S x y hS
  obtain ⟨hxy', heS'⟩ := hread S' x' y' hS'
  have htoP : toPoint W x y = WeierstrassCurve.Affine.Point.some x y hxy := dif_pos hxy
  have htoP' : toPoint W x' y' = WeierstrassCurve.Affine.Point.some x' y' hxy' := dif_pos hxy'
  have hval : ev T (schemeHomOverComp ι hψ (zlinComb (𝒢 T W hΔ) S S' a b)) = a • toPoint W x y + b • toPoint W x' y' := by
    rw [hlin, heS, heS', htoP, htoP']
    rfl
  refine ⟨?_, ?_⟩
  · intro h0
    apply hinj
    apply (ev T).injective
    rw [hval, h0, hone]
    rfl
  · intro xr yr hr hsum
    obtain ⟨Sr, hSr⟩ := ((equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).1 xr yr).mp hr.left
    obtain ⟨hxyr, heSr⟩ := hread Sr xr yr hSr
    have heq : zlinComb (𝒢 T W hΔ) S S' a b = Sr := by
      apply hinj
      apply (ev T).injective
      rw [hval, hsum, heSr]
    rw [heq]; exact hSr

end

end S_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_zlinComb_of_isSectionThrough
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_zlinComb_of_isSectionThrough (solution)
