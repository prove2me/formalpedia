-- Prove2me | solution 1 for WeierstrassProjModel.variableChange_eq_one_of_projMap_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/871bb66e-a03b-51b9-9e76-335645bb7855

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Mathlib
import Definitions.Def_WeierstrassCurve_PointChart
import Theorems.Thm_WeierstrassProjModel_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom
import Theorems.Thm_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_variableChange_eq_one_of_projMap_eq_id

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra
open HomogeneousLocalization WeierstrassCurve.DrinfeldGlobal

set_option maxHeartbeats 6400000 in

theorem solution
    (T : Type) [CommRing T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (C : WeierstrassCurve.VariableChange T) (hC : C • W = W)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (C • W).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hφC : IsVariableChangeHom W.toProjective C φ)
    (hid : eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hC)).symm ≫ Proj.map φ hφ = 𝟙 _) :
    C = 1 := by
  classical

  obtain ⟨a, hsq, hsc, hax, hay⟩ :=
    WeierstrassProjModel.exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom
      W.toProjective C φ hφ hφC

  have key : ∀ (V : WeierstrassCurve.Projective T) (hV : W.toProjective = V)
      (φ₂ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR V)
      (hφ₂ : HomogeneousIdeal.irrelevant (projModelGradingCR V) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ₂)
      (a₂ : ZChartRing W.toProjective →+* ZChartRing V),
      zChartι V ≫ Proj.map φ₂ hφ₂ = Spec.map (CommRingCat.ofHom a₂) ≫ zChartι W.toProjective →
      eqToHom (congrArg projModelCR hV) ≫ Proj.map φ₂ hφ₂ = 𝟙 _ →
      a₂ (xOverZ W.toProjective) =
        fromZeroRingHom (projModelGradingCR V) _ (algebraMap T ((projModelGradingCR V) 0) ((C.u : T) ^ 2)) * xOverZ V +
        fromZeroRingHom (projModelGradingCR V) _ (algebraMap T ((projModelGradingCR V) 0) C.r) →
      a₂ (yOverZ W.toProjective) =
        fromZeroRingHom (projModelGradingCR V) _ (algebraMap T ((projModelGradingCR V) 0) ((C.u : T) ^ 3)) * yOverZ V +
        fromZeroRingHom (projModelGradingCR V) _ (algebraMap T ((projModelGradingCR V) 0) ((C.u : T) ^ 2 * C.s)) *
          xOverZ V +
        fromZeroRingHom (projModelGradingCR V) _ (algebraMap T ((projModelGradingCR V) 0) C.t) →
      (xOverZ W.toProjective =
        fromZeroRingHom (projModelGradingCR W.toProjective) _
            (algebraMap T ((projModelGradingCR W.toProjective) 0) ((C.u : T) ^ 2)) * xOverZ W.toProjective +
        fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) C.r)) ∧
      (yOverZ W.toProjective =
        fromZeroRingHom (projModelGradingCR W.toProjective) _
            (algebraMap T ((projModelGradingCR W.toProjective) 0) ((C.u : T) ^ 3)) * yOverZ W.toProjective +
        fromZeroRingHom (projModelGradingCR W.toProjective) _
            (algebraMap T ((projModelGradingCR W.toProjective) 0) ((C.u : T) ^ 2 * C.s)) * xOverZ W.toProjective +
        fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) C.t)) := by
    intro V hV
    subst hV
    intro φ₂ hφ₂ a₂ hsq₂ hid₂ hax₂ hay₂
    have hP : Proj.map φ₂ hφ₂ = 𝟙 _ := by simpa using hid₂
    have hS : Spec.map (CommRingCat.ofHom a₂) = 𝟙 _ := by
      rw [← cancel_mono (zChartι W.toProjective), Category.id_comp, ← hsq₂, hP, Category.comp_id]
    have ha : a₂ = RingHom.id _ := by
      have h := Spec.map_inj.mp (hS.trans (Spec.map_id _).symm)
      exact congrArg CommRingCat.Hom.hom h
    subst ha
    exact ⟨hax₂, hay₂⟩
  obtain ⟨hx, hy⟩ := key (C • W).toProjective (congrArg WeierstrassCurve.toProjective hC).symm φ hφ a hsq hid hax hay

  obtain ⟨f, -, hfcomp, hfmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing W.toProjective

  let f' : ZChartRing W.toProjective →+* W.toProjective.toAffine.CoordinateRing := f
  have hf' : ∀ z, f' z = f z := fun _ => rfl
  have hfc : ∀ b : T, f' (fromZeroRingHom (projModelGradingCR W.toProjective) _
      (algebraMap T ((projModelGradingCR W.toProjective) 0) b)) = WeierstrassCurve.Affine.CoordinateRing.mk W.toProjective.toAffine (_root_.Polynomial.C (_root_.Polynomial.C b)) := by
    intro b
    have h1 := congrArg (fun g : T →+* (_root_.Polynomial (_root_.Polynomial T) ⧸ (Ideal.span {W.toProjective.toAffine.polynomial} : Ideal (_root_.Polynomial (_root_.Polynomial T)))) => g b) hfcomp
    simp only [RingHom.comp_apply] at h1
    rw [hf', h1, ← Ideal.Quotient.mk_comp_algebraMap, RingHom.comp_apply, _root_.Polynomial.algebraMap_apply,
      _root_.Polynomial.algebraMap_apply, Algebra.algebraMap_self_apply]
    rfl
  have hfx : f' (xOverZ W.toProjective) = WeierstrassCurve.Affine.CoordinateRing.mk W.toProjective.toAffine (_root_.Polynomial.C _root_.Polynomial.X) := by
    have h := hfmk 1 (MvPolynomial.X 0) (by simpa using MvPolynomial.isHomogeneous_X T 0)
    rw [MvPolynomial.aeval_X] at h
    exact h
  have hfy : f' (yOverZ W.toProjective) = WeierstrassCurve.Affine.CoordinateRing.mk W.toProjective.toAffine _root_.Polynomial.X := by
    have h := hfmk 1 (MvPolynomial.X 1) (by simpa using MvPolynomial.isHomogeneous_X T 1)
    rw [MvPolynomial.aeval_X] at h
    exact h
  have hx' := congrArg f' hx
  have hy' := congrArg f' hy
  simp only [map_add, map_mul, hfc, hfx, hfy] at hx' hy'

  set p₁ : _root_.Polynomial T :=
    _root_.Polynomial.X - (_root_.Polynomial.C ((C.u : T) ^ 2) * _root_.Polynomial.X + _root_.Polynomial.C C.r) with hp₁
  set p₂ : _root_.Polynomial T :=
    -(_root_.Polynomial.C ((C.u : T) ^ 2 * C.s) * _root_.Polynomial.X + _root_.Polynomial.C C.t) with hp₂
  set q₂ : _root_.Polynomial T := 1 - _root_.Polynomial.C ((C.u : T) ^ 3) with hq₂
  have e₁ : WeierstrassCurve.Affine.CoordinateRing.mk W.toProjective.toAffine (_root_.Polynomial.C p₁) = 0 := by
    have : (_root_.Polynomial.C p₁ : _root_.Polynomial (_root_.Polynomial T)) = _root_.Polynomial.C _root_.Polynomial.X -
        (_root_.Polynomial.C (_root_.Polynomial.C ((C.u : T) ^ 2)) * _root_.Polynomial.C _root_.Polynomial.X +
          _root_.Polynomial.C (_root_.Polynomial.C C.r)) := by
      rw [hp₁, _root_.Polynomial.C_sub, _root_.Polynomial.C_add, _root_.Polynomial.C_mul]
    rw [this, map_sub, map_add, map_mul, sub_eq_zero]
    exact hx'
  have e₂ : WeierstrassCurve.Affine.CoordinateRing.mk W.toProjective.toAffine (_root_.Polynomial.C p₂ + _root_.Polynomial.C q₂ * _root_.Polynomial.X) = 0 := by
    have : (_root_.Polynomial.C p₂ + _root_.Polynomial.C q₂ * _root_.Polynomial.X : _root_.Polynomial (_root_.Polynomial T)) = _root_.Polynomial.X -
        (_root_.Polynomial.C (_root_.Polynomial.C ((C.u : T) ^ 3)) * _root_.Polynomial.X +
          _root_.Polynomial.C (_root_.Polynomial.C ((C.u : T) ^ 2)) * _root_.Polynomial.C (_root_.Polynomial.C C.s) *
            _root_.Polynomial.C _root_.Polynomial.X +
          _root_.Polynomial.C (_root_.Polynomial.C C.t)) := by
      rw [hp₂, hq₂]
      simp only [_root_.Polynomial.C_neg, _root_.Polynomial.C_add, _root_.Polynomial.C_mul, _root_.Polynomial.C_sub,
        _root_.Polynomial.C_1]
      ring
    rw [this, map_sub, map_add, map_add, map_mul, map_mul, map_mul, sub_eq_zero]
    exact hy'
  have hrel₁ : p₁ • (1 : W.toProjective.toAffine.CoordinateRing) + (0 : _root_.Polynomial T) • WeierstrassCurve.Affine.CoordinateRing.mk W.toProjective.toAffine _root_.Polynomial.X = 0 := by
    rw [zero_smul, add_zero, WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]; exact e₁
  have hrel₂ : p₂ • (1 : W.toProjective.toAffine.CoordinateRing) + q₂ • WeierstrassCurve.Affine.CoordinateRing.mk W.toProjective.toAffine _root_.Polynomial.X = 0 := by
    rw [WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul, mul_one, ← map_mul,
      ← map_add]; exact e₂
  obtain ⟨hp₁0, -⟩ := WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero (W' := W.toProjective.toAffine) hrel₁
  obtain ⟨hp₂0, hq₂0⟩ := WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero (W' := W.toProjective.toAffine) hrel₂

  have c₁ : ∀ n, p₁.coeff n = 0 := fun n => by rw [hp₁0, _root_.Polynomial.coeff_zero]
  have c₂ : ∀ n, p₂.coeff n = 0 := fun n => by rw [hp₂0, _root_.Polynomial.coeff_zero]
  have c₃ : ∀ n, q₂.coeff n = 0 := fun n => by rw [hq₂0, _root_.Polynomial.coeff_zero]
  have hu2 : (C.u : T) ^ 2 = 1 := by
    have h := c₁ 1
    simp [hp₁, _root_.Polynomial.coeff_X, _root_.Polynomial.coeff_C, _root_.Polynomial.coeff_one, -_root_.Polynomial.C_pow, -map_pow] at h
    first
      | exact h.symm
      | exact h
      | exact (sub_eq_zero.mp h).symm
      | exact sub_eq_zero.mp h
      | linear_combination h
      | linear_combination (-1 : T) * h
  have hr : C.r = 0 := by
    have h := c₁ 0
    simp [hp₁, _root_.Polynomial.coeff_X, _root_.Polynomial.coeff_C, _root_.Polynomial.coeff_one, -_root_.Polynomial.C_pow, -map_pow] at h
    first
      | exact h
      | exact neg_eq_zero.mp h
      | linear_combination h
      | linear_combination (-1 : T) * h
  have hu3 : (C.u : T) ^ 3 = 1 := by
    have h := c₃ 0
    simp [hq₂, _root_.Polynomial.coeff_C, _root_.Polynomial.coeff_one, -_root_.Polynomial.C_pow, -map_pow] at h
    first
      | exact h.symm
      | exact h
      | exact (sub_eq_zero.mp h).symm
      | exact sub_eq_zero.mp h
      | linear_combination h
      | linear_combination (-1 : T) * h
  have ht : C.t = 0 := by
    have h := c₂ 0
    simp [hp₂, _root_.Polynomial.coeff_X, _root_.Polynomial.coeff_C, _root_.Polynomial.coeff_one, -_root_.Polynomial.C_pow, -map_pow, -_root_.Polynomial.C_mul, -map_mul] at h
    first
      | exact h
      | exact neg_eq_zero.mp h
      | linear_combination h
      | linear_combination (-1 : T) * h
  have hus : (C.u : T) ^ 2 * C.s = 0 := by
    have h := c₂ 1
    simp [hp₂, _root_.Polynomial.coeff_X, _root_.Polynomial.coeff_C, _root_.Polynomial.coeff_one, -_root_.Polynomial.C_pow, -map_pow, -_root_.Polynomial.C_mul, -map_mul] at h
    first
      | exact h
      | exact neg_eq_zero.mp h
      | (rw [hu2, one_mul]; first | exact h | exact neg_eq_zero.mp h | linear_combination h)
      | linear_combination h
      | linear_combination (-1 : T) * h
  have hs : C.s = 0 := by rw [hu2, one_mul] at hus; exact hus
  have hu : (C.u : T) = 1 := by
    calc (C.u : T) = C.u * (C.u : T) ^ 2 := by rw [hu2, mul_one]
      _ = (C.u : T) ^ 3 := by ring
      _ = 1 := hu3
  have hC' : C = ⟨C.u, C.r, C.s, C.t⟩ := rfl
  rw [hC', WeierstrassCurve.VariableChange.one_def]
  simp only [WeierstrassCurve.VariableChange.mk.injEq]
  exact ⟨Units.val_eq_one.mp hu, hr, hs, ht⟩

end S_WeierstrassProjModel_variableChange_eq_one_of_projMap_eq_id
end P2MW
export P2MW.S_WeierstrassProjModel_variableChange_eq_one_of_projMap_eq_id (solution)
