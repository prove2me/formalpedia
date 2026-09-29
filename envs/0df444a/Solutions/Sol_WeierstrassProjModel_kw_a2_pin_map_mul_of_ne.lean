-- Prove2me | solution 1 for WeierstrassProjModel.kw_a2_pin_map_mul_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7a377967-8b47-5fd7-929b-9c6aca4377c7

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_kw_a2_exists_sixU_ne_zero_of_pointClass_ne
import Theorems.Thm_WeierstrassProjModel_kw_a2_sixU_class_eq_addMap_of_delta_ne_zero
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_a2_pin_map_mul_of_ne

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option Elab.async false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve MvPolynomial
open HomogeneousLocalization
open WeierstrassProjModel NeronModelInfra
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (F : Type u) [Field F] [Algebra R F]

set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "coverE" => (projModelAffineOpenCoverCR R W.toProjective).openCover
set_option quotPrecheck false in
local notation "t_F" => kw_lrAptb_tF (R := R) F
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective

section LiftAux

variable (i j : Fin 3)

theorem aux_chartIso_inv_fst :
    (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ pullback.fst _ _
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := 𝒜 i) (B := 𝒜 j))) := by
  simp only [kwProjPullbackChartIsoCR, Iso.trans_inv, Category.assoc]
  rw [pullback.congrHom_inv]
  erw [pullback.lift_fst]
  rw [Category.comp_id]
  exact pullbackSpecIso_inv_fst R (𝒜 i) (𝒜 j)

theorem aux_chartIso_inv_snd :
    (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ pullback.snd _ _
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R) (A := 𝒜 i) (B := 𝒜 j)).toRingHom) := by
  simp only [kwProjPullbackChartIsoCR, Iso.trans_inv, Category.assoc]
  rw [pullback.congrHom_inv]
  erw [pullback.lift_snd]
  rw [Category.comp_id]
  exact pullbackSpecIso_inv_snd R (𝒜 i) (𝒜 j)

set_option maxHeartbeats 25600000 in
private theorem aux_liftAddMor_fst :
    (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j)
        ≫ pullback.fst _ _
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := 𝒜 i) (B := 𝒜 j)))
          ≫ (coverE).f i := by
  simp only [kwProjPullbackOpenCoverCR, Scheme.Pullback.openCoverOfLeftRight_f]
  erw [pullback.lift_fst]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (coverE).f i) (aux_chartIso_inv_fst W i j))

set_option maxHeartbeats 25600000 in
private theorem aux_liftAddMor_snd :
    (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j)
        ≫ pullback.snd _ _
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R) (A := 𝒜 i) (B := 𝒜 j)).toRingHom)
          ≫ (coverE).f j := by
  simp only [kwProjPullbackOpenCoverCR, Scheme.Pullback.openCoverOfLeftRight_f]
  erw [pullback.lift_snd]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (coverE).f j) (aux_chartIso_inv_snd W i j))

set_option maxHeartbeats 25600000 in
private theorem aux_prod_fst (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom)
        ≫ (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j)
        ≫ pullback.fst _ _
      = Spec.map (CommRingCat.ofHom ψᵢ.toRingHom) ≫ (coverE).f i := by
  have hcompL : (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := 𝒜 i) (B := 𝒜 j))
      = ψᵢ.toRingHom :=
    RingHom.ext fun a =>
      (Algebra.TensorProduct.productMap_apply_tmul ψᵢ ψⱼ a 1).trans
        (by rw [map_one, mul_one]; rfl)
  rw [aux_liftAddMor_fst W i j, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, hcompL]

set_option maxHeartbeats 25600000 in
private theorem aux_prod_snd (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom)
        ≫ (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j)
        ≫ pullback.snd _ _
      = Spec.map (CommRingCat.ofHom ψⱼ.toRingHom) ≫ (coverE).f j := by
  have hcompR : (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := 𝒜 i) (B := 𝒜 j)).toRingHom
      = ψⱼ.toRingHom :=
    RingHom.ext fun a =>
      (Algebra.TensorProduct.productMap_apply_tmul ψᵢ ψⱼ 1 a).trans
        (by rw [map_one, one_mul]; rfl)
  rw [aux_liftAddMor_snd W i j, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, hcompR]

private theorem aux_assoc4 {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ : C}
    (a : O₁ ⟶ O₂) (b : O₂ ⟶ O₃) (c : O₃ ⟶ O₄) (d : O₄ ⟶ O₅) :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d :=
  (Category.assoc a (b ≫ c) d).trans (congrArg (a ≫ ·) (Category.assoc b c d))

set_option maxHeartbeats 25600000 in
private theorem aux_leg_fst (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F)
    (x y : SchemeHomOver (t_F) π)
    (hfacx : x.1 = Spec.map (CommRingCat.ofHom ψᵢ.toRingHom) ≫ (coverE).f i) :
    pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ pullback.fst _ _
      = ( Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom)
          ≫ (kwProjPullbackChartIsoCR R W.toProjective i j).inv
          ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j)) ≫ pullback.fst _ _ :=
  (pullback.lift_fst _ _ _).trans
    (hfacx.trans ((aux_assoc4 _ _ _ _).trans (aux_prod_fst W F i j ψᵢ ψⱼ)).symm)

set_option maxHeartbeats 25600000 in
private theorem aux_leg_snd (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F)
    (x y : SchemeHomOver (t_F) π)
    (hfacy : y.1 = Spec.map (CommRingCat.ofHom ψⱼ.toRingHom) ≫ (coverE).f j) :
    pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ pullback.snd _ _
      = ( Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom)
          ≫ (kwProjPullbackChartIsoCR R W.toProjective i j).inv
          ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j)) ≫ pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans
    (hfacy.trans ((aux_assoc4 _ _ _ _).trans (aux_prod_snd W F i j ψᵢ ψⱼ)).symm)

set_option maxHeartbeats 25600000 in

private theorem aux_lift (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F)
    (x y : SchemeHomOver (t_F) π)
    (hfacx : x.1 = Spec.map (CommRingCat.ofHom ψᵢ.toRingHom) ≫ (coverE).f i)
    (hfacy : y.1 = Spec.map (CommRingCat.ofHom ψⱼ.toRingHom) ≫ (coverE).f j) :
    pullback.lift x.1 y.1 (x.2.trans y.2.symm)
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom)
          ≫ (kwProjPullbackChartIsoCR R W.toProjective i j).inv
          ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j) :=
  pullback.hom_ext (aux_leg_fst W F i j ψᵢ ψⱼ x y hfacx)
    (aux_leg_snd W F i j ψᵢ ψⱼ x y hfacy)

end LiftAux

set_option maxHeartbeats 25600000 in
theorem solution
    (hΔ : algebraMap R F W.Δ ≠ 0)
    (m : pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ⟶ projModelCR W.toProjective)
    (hmpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap W i j l
        ≫ (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j) ≫ m
      = kw_lrSixU_toE W i j l)
    (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F)
    (k : Fin 3) (ψₖ : (𝒜 k) →ₐ[R] F)
    (x y : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective))
    (hfacx : x.1 = Spec.map (CommRingCat.ofHom ψᵢ.toRingHom)
        ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i)
    (hfacy : y.1 = Spec.map (CommRingCat.ofHom ψⱼ.toRingHom)
        ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f j)
    (hfacsum : pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m
      = Spec.map (CommRingCat.ofHom ψₖ.toRingHom)
          ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f k)
    (hne : (⟦kw_lrApt_chartEval W F i ψᵢ⟧ : WeierstrassCurve.Projective.PointClass F)
           ≠ ⟦kw_lrApt_chartEval W F j ψⱼ⟧) :
    (⟦kw_lrApt_chartEval W F k ψₖ⟧ : WeierstrassCurve.Projective.PointClass F)
      = (kw_lrApt_WF W F).addMap
          ⟦kw_lrApt_chartEval W F i ψᵢ⟧ ⟦kw_lrApt_chartEval W F j ψⱼ⟧ := by

  obtain ⟨l, hl⟩ := kw_a2_exists_sixU_ne_zero_of_pointClass_ne W F hΔ i j ψᵢ ψⱼ hne
  have hu : IsUnit ((Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l)) :=
    isUnit_iff_ne_zero.mpr hl

  have hlift := aux_lift W F i j ψᵢ ψⱼ x y hfacx hfacy

  have hfact : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom)
      = Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.lift (kw_lrSixU W i j l)
            (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
          ≫ kw_lrSixU_locMap W i j l := by
    rw [kw_lrSixU_locMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      IsLocalization.Away.lift_comp]

  have hchain : pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m
      = Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.lift (kw_lrSixU W i j l)
            (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
          ≫ kw_lrSixU_toE W i j l := by

    rw [hlift, Category.assoc, Category.assoc, hfact, Category.assoc, hmpin i j l]
  have hfac : Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.lift (kw_lrSixU W i j l)
            (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
          ≫ kw_lrSixU_toE W i j l
        = Spec.map (CommRingCat.ofHom ψₖ.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f k :=
    hchain.symm.trans hfacsum
  exact kw_a2_sixU_class_eq_addMap_of_delta_ne_zero W F hΔ i j ψᵢ ψⱼ l hu k ψₖ hfac

end

end S_WeierstrassProjModel_kw_a2_pin_map_mul_of_ne
end P2MW
export P2MW.S_WeierstrassProjModel_kw_a2_pin_map_mul_of_ne (solution)
