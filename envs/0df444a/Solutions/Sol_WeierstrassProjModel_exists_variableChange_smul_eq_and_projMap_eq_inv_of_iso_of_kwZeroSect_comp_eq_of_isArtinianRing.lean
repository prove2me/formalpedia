-- Prove2me | solution 1 for WeierstrassProjModel.exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3f7f5cdd-5825-53b2-8756-2789b0ebdcbd

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_FormalGroup_NSeries
import Theorems.Thm_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing
import Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_of_algHom_coordinateRing_triangular
import Theorems.Thm_WeierstrassProjModel_hom_ext_of_zChartIota_comp_eq
import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_powerSeries
import Theorems.Thm_WeierstrassProjModel_coeff_laurent_zChart_of_iso_of_kwZeroSect_comp_eq
import Theorems.Thm_WeierstrassProjModel_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom
import Theorems.Thm_WeierstrassProjModel_exists_ringEquiv_zChartRing_of_iso_of_kwZeroSect_comp_eq
import Theorems.Thm_WeierstrassProjModel_exists_laurent_zChartRing_filtration
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

p2m_open "HomogeneousLocalization Polynomial AlgebraicGeometry.Polynomial"

namespace WMLocal
variable {T : Type} [CommRing T]

noncomputable abbrev cZ (V : WeierstrassCurve T) : T →+* ZChartRing V.toProjective :=
  (fromZeroRingHom (projModelGradingCR V.toProjective) _).comp (algebraMap T ((projModelGradingCR V.toProjective) 0))
end WMLocal

namespace WMLocal

section Ext

theorem zChart_ringHom_ext {T : Type} [CommRing T] (V : WeierstrassCurve.Projective T) {B : Type} [CommRing B]
    (g₁ g₂ : ZChartRing V →+* B) (h0 : g₁.comp (((fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0)))) = g₂.comp (((fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0)))))
    (hx : g₁ (xOverZ V) = g₂ (xOverZ V)) (hy : g₁ (yOverZ V) = g₂ (yOverZ V)) : g₁ = g₂ := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V
  let e := RingEquiv.ofBijective f hbij
  have hx' : e.symm (Ideal.Quotient.mk _ (Polynomial.C Polynomial.X)) = xOverZ V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this.symm
  have hy' : e.symm (Ideal.Quotient.mk _ Polynomial.X) = yOverZ V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.head_cons] at this
    exact this.symm
  have hr : ∀ r : T, e.symm (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C r))) = ((fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0))) r := by
    intro r
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.congr_fun hcomp r).symm
  suffices h : (g₁.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) =
      (g₂.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) by
    have h' : g₁.comp e.symm.toRingHom = g₂.comp e.symm.toRingHom := Ideal.Quotient.ringHom_ext h
    ext x
    have := RingHom.congr_fun h' (e x)
    rwa [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply] at this
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · ext r
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hr]
      exact RingHom.congr_fun h0 r
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hx']
      exact hx
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hy']
    exact hy

end Ext

section W4

theorem triangular_of_coeff {T : Type*} [CommRing T] {A A' : Type*} [CommRing A] [CommRing A']
    (c : T →+* A) (x y : A) (x' y' : A') (g : A' →+* A) (lam : A →+* LaurentSeries T)
    (hF2 : ∀ a : A, (∀ n : ℤ, n < -2 → (lam a).coeff n = 0) →
      ∃ c₀ c₁ : T, a = c c₁ * x + c c₀ ∧ c₁ = (lam a).coeff (-2))
    (hF3 : ∀ a : A, (∀ n : ℤ, n < -3 → (lam a).coeff n = 0) →
      ∃ c₀ c₁ c₂ : T, a = c c₂ * y + c c₁ * x + c c₀ ∧ c₂ = -((lam a).coeff (-3)))
    (hx₁ : ∀ n : ℤ, n < -2 → (lam (g x')).coeff n = 0) (hx₂ : IsUnit ((lam (g x')).coeff (-2)))
    (hy₁ : ∀ n : ℤ, n < -3 → (lam (g y')).coeff n = 0) (hy₂ : IsUnit ((lam (g y')).coeff (-3))) :
    ∃ (v₁ v₂ : Tˣ) (r s' t : T),
      g x' = c v₁ * x + c r ∧ g y' = c v₂ * y + c s' * x + c t := by
  obtain ⟨p₀, p₁, hex, hp₁⟩ := hF2 (g x') hx₁
  obtain ⟨q₀, q₁, q₂, hey, hq₂⟩ := hF3 (g y') hy₁
  have hu₁ : IsUnit p₁ := hp₁ ▸ hx₂
  have hu₂ : IsUnit q₂ := by rw [hq₂]; exact hy₂.neg
  refine ⟨hu₁.unit, hu₂.unit, p₀, q₁, q₀, ?_, ?_⟩
  · rw [hu₁.unit_spec, hex]
  · rw [hu₂.unit_spec, hey]

end W4

section Generic

theorem symm_triangular {T : Type*} [CommRing T] {A A' : Type*} [CommRing A] [CommRing A']
    (c : T →+* A) (c' : T →+* A') (x y : A) (x' y' : A') (e : A' ≃+* A) (he : ∀ t, e (c' t) = c t)
    (v₁ v₂ : Tˣ) (r s' t : T)
    (hx : e x' = c v₁ * x + c r) (hy : e y' = c v₂ * y + c s' * x + c t) :
    e.symm x = c' ↑v₁⁻¹ * x' + c' (-(↑v₁⁻¹ * r)) ∧
      e.symm y = c' ↑v₂⁻¹ * y' + c' (-(↑v₂⁻¹ * s' * ↑v₁⁻¹)) * x' + c' (↑v₂⁻¹ * (s' * ↑v₁⁻¹ * r - t)) := by
  have he' : ∀ t, e.symm (c t) = c' t := fun t => by rw [← he, RingEquiv.symm_apply_apply]
  have hx' : x' = c' v₁ * e.symm x + c' r := by
    have := congrArg e.symm hx
    rwa [RingEquiv.symm_apply_apply, map_add, map_mul, he', he'] at this
  have hy' : y' = c' v₂ * e.symm y + c' s' * e.symm x + c' t := by
    have := congrArg e.symm hy
    rwa [RingEquiv.symm_apply_apply, map_add, map_add, map_mul, map_mul, he', he', he'] at this
  have hv₁ : c' ↑v₁⁻¹ * c' v₁ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hv₂ : c' ↑v₂⁻¹ * c' v₂ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have ex0 : e.symm x = c' ↑v₁⁻¹ * x' - c' ↑v₁⁻¹ * c' r := by
    linear_combination (-(c' ↑v₁⁻¹)) * hx' + (-(e.symm x)) * hv₁
  have ey0 : e.symm y = c' ↑v₂⁻¹ * y' - c' ↑v₂⁻¹ * c' s' * c' ↑v₁⁻¹ * x' +
      c' ↑v₂⁻¹ * (c' s' * c' ↑v₁⁻¹ * c' r - c' t) := by
    linear_combination (-(c' ↑v₂⁻¹)) * hy' + (-(e.symm y)) * hv₂ + (-(c' ↑v₂⁻¹ * c' s')) * ex0
  constructor
  · simp only [map_neg, map_mul]
    linear_combination ex0
  · simp only [map_neg, map_mul, map_sub]
    linear_combination ey0

theorem exists_algHom_triangular_of_charts {T : Type*} [CommRing T] {A A' C C' : Type*}
    [CommRing A] [CommRing A'] [CommRing C] [CommRing C'] [Algebra T C] [Algebra T C']
    (c : T →+* A) (c' : T →+* A') (x y : A) (x' y' : A')
    (fA : A →+* C) (hfA : Function.Bijective fA) (hfAc : fA.comp c = algebraMap T C)
    (fA' : A' →+* C') (hfA'c : fA'.comp c' = algebraMap T C')
    (ε : A →+* A') (hε : ∀ t, ε (c t) = c' t)
    (a b k d m : T) (hx : ε x = c' a * x' + c' b) (hy : ε y = c' k * y' + c' d * x' + c' m) :
    ∃ g : C →ₐ[T] C', g (fA x) = a • fA' x' + algebraMap T C' b ∧
      g (fA y) = k • fA' y' + d • fA' x' + algebraMap T C' m := by
  let E : A ≃+* C := RingEquiv.ofBijective fA hfA
  have hE : ∀ z, E.symm (fA z) = z := fun z => E.symm_apply_apply z
  have hc : ∀ t, fA (c t) = algebraMap T C t := fun t => RingHom.congr_fun hfAc t
  have hc' : ∀ t, fA' (c' t) = algebraMap T C' t := fun t => RingHom.congr_fun hfA'c t
  let g₀ : C →+* C' := fA'.comp (ε.comp E.symm.toRingHom)
  have hg₀ : ∀ z, g₀ (fA z) = fA' (ε z) := fun z => by
    show fA' (ε (E.symm (fA z))) = _; rw [hE]
  let g : C →ₐ[T] C' :=
    { toRingHom := g₀
      commutes' := fun t => by
        show g₀ (algebraMap T C t) = algebraMap T C' t
        rw [← hc, hg₀, hε, hc'] }
  refine ⟨g, ?_, ?_⟩
  · show g₀ (fA x) = _
    rw [hg₀, hx, map_add, map_mul, hc', hc', Algebra.smul_def]
  · show g₀ (fA y) = _
    rw [hg₀, hy, map_add, map_add, map_mul, map_mul, hc', hc', hc', Algebra.smul_def, Algebra.smul_def]

end Generic

section Charts

variable {T : Type} [CommRing T]

theorem exists_zChart_to_coordinateRing (V : WeierstrassCurve T) :
    ∃ f : ZChartRing V.toProjective →+* V.toAffine.CoordinateRing, Function.Bijective f ∧
      f.comp (cZ V) = algebraMap T V.toAffine.CoordinateRing ∧
      f (xOverZ V.toProjective) = WeierstrassCurve.Affine.CoordinateRing.mk V (C X) ∧
      f (yOverZ V.toProjective) = WeierstrassCurve.Affine.CoordinateRing.mk V X := by
  obtain ⟨f, hbij, hc, hval⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V.toProjective
  refine ⟨f, hbij, hc, ?_, ?_⟩
  · have := hval 1 (MvPolynomial.X 0) (by simpa using MvPolynomial.isHomogeneous_X T 0)
    refine (Eq.trans ?_ this).trans ?_
    · rfl
    · show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
      congr 1
      simp [MvPolynomial.aeval_X]
  · have := hval 1 (MvPolynomial.X 1) (by simpa using MvPolynomial.isHomogeneous_X T 1)
    refine (Eq.trans ?_ this).trans ?_
    · rfl
    · show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
      congr 1
      simp [MvPolynomial.aeval_X]

theorem exists_coordinateRing_algHom_triangular_of_zChart_ringEquiv (W W' : WeierstrassCurve T)
    (e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective) (he : ∀ t, e (cZ W' t) = cZ W t)
    (v₁ v₂ : Tˣ) (r s' t : T)
    (hx : e (xOverZ W'.toProjective) = cZ W v₁ * xOverZ W.toProjective + cZ W r)
    (hy : e (yOverZ W'.toProjective) = cZ W v₂ * yOverZ W.toProjective + cZ W s' * xOverZ W.toProjective + cZ W t) :
    ∃ g : W.toAffine.CoordinateRing →ₐ[T] W'.toAffine.CoordinateRing,
      g (WeierstrassCurve.Affine.CoordinateRing.mk W (C X)) =
        ((v₁⁻¹ : Tˣ) : T) • WeierstrassCurve.Affine.CoordinateRing.mk W' (C X) + algebraMap T _ (-(↑v₁⁻¹ * r)) ∧
      g (WeierstrassCurve.Affine.CoordinateRing.mk W X) =
        ((v₂⁻¹ : Tˣ) : T) • WeierstrassCurve.Affine.CoordinateRing.mk W' X +
          (-(↑v₂⁻¹ * s' * ↑v₁⁻¹)) • WeierstrassCurve.Affine.CoordinateRing.mk W' (C X) +
          algebraMap T _ (↑v₂⁻¹ * (s' * ↑v₁⁻¹ * r - t)) := by
  obtain ⟨fW, hbW, hcW, hxW, hyW⟩ := exists_zChart_to_coordinateRing W
  obtain ⟨fW', -, hcW', hxW', hyW'⟩ := exists_zChart_to_coordinateRing W'
  obtain ⟨ex, ey⟩ := symm_triangular (cZ W) (cZ W') (xOverZ W.toProjective) (yOverZ W.toProjective)
    (xOverZ W'.toProjective) (yOverZ W'.toProjective) e he v₁ v₂ r s' t hx hy
  have he' : ∀ t, e.symm (cZ W t) = cZ W' t := fun t => by rw [← he, RingEquiv.symm_apply_apply]
  obtain ⟨g, hgx, hgy⟩ := exists_algHom_triangular_of_charts (cZ W) (cZ W') (xOverZ W.toProjective)
    (yOverZ W.toProjective) (xOverZ W'.toProjective) (yOverZ W'.toProjective) fW hbW hcW fW' hcW'
    e.symm.toRingHom he' _ _ _ _ _ ex ey
  rw [hxW, hxW'] at hgx
  rw [hyW, hyW', hxW'] at hgy
  exact ⟨g, hgx, hgy⟩

end Charts

end WMLocal

open WMLocal HomogeneousLocalization in
open IsLocalRing in

theorem solution
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T]
    (W W' : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (hΔ' : IsUnit W'.Δ)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ (C : WeierstrassCurve.VariableChange T) (hC : C • W = W')
      (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (C • W).toProjective)
      (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ),
      IsVariableChangeHom W.toProjective C φ ∧
      eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hC)).symm ≫ Proj.map φ hφ = Ψ.inv := by
  classical

  obtain ⟨e, hec, heι⟩ := WeierstrassProjModel.exists_ringEquiv_zChartRing_of_iso_of_kwZeroSect_comp_eq T W W' Ψ hΨ hΨO

  obtain ⟨Φ, hΦc, hΦx, hΦz⟩ := WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_powerSeries W
  obtain ⟨lam, hlc, hlx, hly, hF2, hF3⟩ := WeierstrassProjModel.exists_laurent_zChartRing_filtration T W Φ hΦc hΦx hΦz

  obtain ⟨hx₁, hx₂, hy₁, hy₂⟩ := WeierstrassProjModel.coeff_laurent_zChart_of_iso_of_kwZeroSect_comp_eq T W W' Ψ hΨ hΨO
    e.toRingHom heι Φ hΦc hΦx hΦz lam hlc hlx hly

  obtain ⟨v₁, v₂, r, s', t, hex, hey⟩ := WMLocal.triangular_of_coeff (WMLocal.cZ W) (xOverZ W.toProjective)
    (yOverZ W.toProjective) (xOverZ W'.toProjective) (yOverZ W'.toProjective) e.toRingHom lam hF2 hF3 hx₁ hx₂ hy₁ hy₂

  obtain ⟨g, hgx, hgy⟩ := WMLocal.exists_coordinateRing_algHom_triangular_of_zChart_ringEquiv W W' e hec v₁ v₂ r s' t hex hey
  obtain ⟨ex, ey⟩ := WMLocal.symm_triangular (WMLocal.cZ W) (WMLocal.cZ W') (xOverZ W.toProjective)
    (yOverZ W.toProjective) (xOverZ W'.toProjective) (yOverZ W'.toProjective) e hec v₁ v₂ r s' t hex hey
  generalize hw₁ : v₁⁻¹ = w₁ at hgx hgy ex ey
  generalize hw₂ : v₂⁻¹ = w₂ at hgx hgy ex ey
  generalize hr₁ : (-(↑w₁ * r) : T) = r₁ at hgx ex
  generalize hs₁ : (-(↑w₂ * s' * ↑w₁) : T) = s₁ at hgy ey
  generalize ht₁ : (↑w₂ * (s' * ↑w₁ * r - t) : T) = t₁ at hgy ey
  obtain ⟨C, hC, ⟨hu2, hu3⟩, hCr, hCs, hCt⟩ :=
    WeierstrassCurve.exists_variableChange_smul_eq_of_algHom_coordinateRing_triangular T W W' g w₁ w₂ r₁ s₁ t₁ hgx hgy
  subst hC

  obtain ⟨φ, hφ, hvc, _, _⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap W.toProjective C
  refine ⟨C, rfl, φ, hφ, hvc, ?_⟩
  simp only [eqToHom_refl, Category.id_comp]

  obtain ⟨a, haι, hac, hax, hay⟩ := WeierstrassProjModel.exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom W.toProjective C φ hφ hvc
  have hec' : ∀ b : T, e.symm (WMLocal.cZ W b) = WMLocal.cZ (C • W) b := fun b => by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (hec b).symm
  have hae : a = e.symm.toRingHom := by
    apply WMLocal.zChart_ringHom_ext W.toProjective
    · refine RingHom.ext fun b => ?_
      change a (WMLocal.cZ W b) = e.symm (WMLocal.cZ W b)
      rw [hec']
      exact hac b
    · change a (xOverZ W.toProjective) = e.symm (xOverZ W.toProjective)
      rw [hax, ex, hu2, hCr]
      rfl
    · change a (yOverZ W.toProjective) = e.symm (yOverZ W.toProjective)
      rw [hay, ey, hCs, hu3, hCt]
      rfl
  apply WeierstrassProjModel.hom_ext_of_zChartIota_comp_eq T (C • W)
  rw [haι, hae]

  have hcomp : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun z => ?_
    show e.symm (e z) = z
    exact e.symm_apply_apply z
  have hee : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, hcomp, Spec.map_id]
  symm
  calc zChartι (C • W).toProjective ≫ Ψ.inv
      = (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) ≫
          zChartι (C • W).toProjective ≫ Ψ.inv := by rw [hee, Category.id_comp]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          ((Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι (C • W).toProjective) ≫ Ψ.inv) := by
        simp only [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ ((zChartι W.toProjective ≫ Ψ.hom) ≫ Ψ.inv) := by rw [heι]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ zChartι W.toProjective := by
        rw [Category.assoc, Ψ.hom_inv_id, Category.comp_id]

end S_WeierstrassProjModel_exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing
end P2MW
export P2MW.S_WeierstrassProjModel_exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing (solution)
