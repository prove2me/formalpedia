-- Prove2me | solution 1 for WeierstrassProjModel.exists_laurent_zChartRing_filtration
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2f226227-55a4-5a3e-97e2-2a04cc2d9a13

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Theorems.Thm_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_laurent_zChartRing_filtration
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace WMLocal

variable {T : Type} [CommRing T]

abbrev cZ (V : WeierstrassCurve T) : T →+* ZChartRing V.toProjective :=
  (fromZeroRingHom (projModelGradingCR V.toProjective) _).comp (algebraMap T (projModelGradingCR V.toProjective 0))

abbrev cY (V : WeierstrassCurve T) : T →+* OriginChartRing V.toProjective :=
  (fromZeroRingHom (projModelGradingCR V.toProjective) _).comp (algebraMap T (projModelGradingCR V.toProjective 0))

abbrev ofPS (T : Type) [CommRing T] : PowerSeries T →+* LaurentSeries T := HahnSeries.ofPowerSeries ℤ T

theorem formalW_eq_X_pow_three_mul (V : WeierstrassCurve T) :
    ∃ v : PowerSeries T, V.formalW = PowerSeries.X ^ 3 * v ∧ PowerSeries.constantCoeff v = 1 := by
  obtain ⟨v, hv⟩ := V.isUnit_wUnitFactor.exists_right_inv
  refine ⟨v, ?_, ?_⟩
  · calc V.formalW = V.formalW * (V.wUnitFactor * v) := by rw [hv, mul_one]
      _ = PowerSeries.X ^ 3 * v := by rw [← mul_assoc, V.formalW_mul_wUnitFactor]
  · have h := congrArg PowerSeries.constantCoeff hv
    rwa [map_mul, V.constantCoeff_wUnitFactor, one_mul, map_one] at h

theorem zChart_ringHom_ext (V : WeierstrassCurve T) {B : Type} [CommRing B]
    (g₁ g₂ : ZChartRing V.toProjective →+* B) (h0 : g₁.comp (cZ V) = g₂.comp (cZ V))
    (hx : g₁ (xOverZ V.toProjective) = g₂ (xOverZ V.toProjective))
    (hy : g₁ (yOverZ V.toProjective) = g₂ (yOverZ V.toProjective)) : g₁ = g₂ := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V.toProjective
  let e := RingEquiv.ofBijective f hbij
  have hx' : e.symm (Ideal.Quotient.mk _ (Polynomial.C Polynomial.X)) = xOverZ V.toProjective := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this.symm
  have hy' : e.symm (Ideal.Quotient.mk _ Polynomial.X) = yOverZ V.toProjective := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one] at this
    exact this.symm
  have hr : ∀ r : T, e.symm (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C r))) = cZ V r := by
    intro r
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.congr_fun hcomp r).symm
  suffices h : (g₁.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) =
      (g₂.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) by
    have h' : g₁.comp e.symm.toRingHom = g₂.comp e.symm.toRingHom := Ideal.Quotient.ringHom_ext h
    ext a
    have := RingHom.congr_fun h' (e a)
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

section laurent
variable (V : WeierstrassCurve T)

theorem single_one_mul_single_neg_one :
    (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) * HahnSeries.single (-1 : ℤ) (1 : T) = 1 := by
  rw [HahnSeries.single_mul_single, mul_one]; norm_num

theorem single_neg (n : ℕ) :
    (HahnSeries.single (-(n : ℤ)) (1 : T) : LaurentSeries T) = HahnSeries.single (-1 : ℤ) (1 : T) ^ n := by
  rw [HahnSeries.single_pow, one_pow]; congr 1; simp

theorem single_neg_two :
    (HahnSeries.single (-2 : ℤ) (1 : T) : LaurentSeries T) = HahnSeries.single (-1 : ℤ) (1 : T) ^ 2 := single_neg 2

theorem single_neg_three :
    (HahnSeries.single (-3 : ℤ) (1 : T) : LaurentSeries T) = HahnSeries.single (-1 : ℤ) (1 : T) ^ 3 := single_neg 3

theorem single_one_pow_three_mul_single_neg_three :
    (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) ^ 3 * HahnSeries.single (-3 : ℤ) (1 : T) = 1 := by
  rw [single_neg_three]
  calc (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) ^ 3 * HahnSeries.single (-1 : ℤ) (1 : T) ^ 3
      = (HahnSeries.single (1 : ℤ) (1 : T) * HahnSeries.single (-1 : ℤ) (1 : T)) ^ 3 := by ring
    _ = 1 := by rw [single_one_mul_single_neg_one, one_pow]

theorem laurent_equation :
    ((V.map (HahnSeries.C : T →+* LaurentSeries T)).toAffine.polynomial).evalEval
      (ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T))
      (-(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T))) = 0 := by
  set U : LaurentSeries T := ofPS T V.wUnitFactor with hU
  set F : LaurentSeries T := ofPS T V.formalW with hF
  set Zp : LaurentSeries T := HahnSeries.single (1 : ℤ) (1 : T) with hZp
  set Zm : LaurentSeries T := HahnSeries.single (-1 : ℤ) (1 : T) with hZm
  have hpm : Zp * Zm = 1 := single_one_mul_single_neg_one
  have h2 : (HahnSeries.single (-2 : ℤ) (1 : T) : LaurentSeries T) = Zm ^ 2 := single_neg 2
  have h3 : (HahnSeries.single (-3 : ℤ) (1 : T) : LaurentSeries T) = Zm ^ 3 := single_neg 3
  rw [h2, h3]
  set ι : LaurentSeries T := U * Zm ^ 3 with hι
  have hFU : F * U = Zp ^ 3 := by
    rw [hF, hU, ← map_mul, V.formalW_mul_wUnitFactor, map_pow, HahnSeries.ofPowerSeries_X]
  have hFι : F * ι = 1 := by
    rw [hι, ← mul_assoc, hFU]
    calc Zp ^ 3 * Zm ^ 3 = (Zp * Zm) ^ 3 := by ring
      _ = 1 := by rw [hpm, one_pow]
  have hx : U * Zm ^ 2 = ι * Zp := by
    rw [hι]
    calc U * Zm ^ 2 = U * Zm ^ 2 * (Zp * Zm) := by rw [hpm, mul_one]
      _ = U * Zm ^ 3 * Zp := by ring
  have hrel : F = Zp ^ 3 + HahnSeries.C V.a₁ * Zp * F + HahnSeries.C V.a₂ * Zp ^ 2 * F
      + HahnSeries.C V.a₃ * F ^ 2 + HahnSeries.C V.a₄ * Zp * F ^ 2 + HahnSeries.C V.a₆ * F ^ 3 := by
    have h := congrArg (ofPS T) V.formalW_eq
    simp only [map_add, map_mul, map_pow, HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C] at h
    rw [hF, hZp]
    exact h
  rw [WeierstrassCurve.Affine.evalEval_polynomial]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆]
  rw [hx]
  linear_combination (ι ^ 3) * hrel
    - (ι ^ 2 - HahnSeries.C V.a₁ * Zp * ι ^ 2 - HahnSeries.C V.a₂ * Zp ^ 2 * ι ^ 2
        - HahnSeries.C V.a₃ * ι * (ι * F + 1)
        - HahnSeries.C V.a₄ * Zp * ι * (ι * F + 1)
        - HahnSeries.C V.a₆ * (ι ^ 2 * F ^ 2 + ι * F + 1)) * hFι

end laurent

section embed
variable (V : WeierstrassCurve T)

theorem exists_laurentEmbedding_core :
    ∃ lam : ZChartRing V.toProjective →+* LaurentSeries T,
      (∀ t, lam (cZ V t) = HahnSeries.C t) ∧
      lam (xOverZ V.toProjective) = ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T) ∧
      lam (yOverZ V.toProjective) = -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T)) := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V.toProjective
  set xL : LaurentSeries T := ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T) with hxL
  set yL : LaurentSeries T := -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T)) with hyL
  let ev : Polynomial (Polynomial T) →+* LaurentSeries T :=
    (Polynomial.evalEvalRingHom xL yL).comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom (HahnSeries.C : T →+* LaurentSeries T)))
  have hevCC : ∀ t : T, ev (Polynomial.C (Polynomial.C t)) = HahnSeries.C t := by
    intro t; simp [ev]
  have hevCX : ev (Polynomial.C Polynomial.X) = xL := by simp [ev]
  have hevX : ev Polynomial.X = yL := by simp [ev]
  have hev : ev (WeierstrassCurve.Affine.polynomial V.toAffine) = 0 := by
    have h1 : ev (WeierstrassCurve.Affine.polynomial V.toAffine)
        = ((V.map (HahnSeries.C : T →+* LaurentSeries T)).toAffine.polynomial).evalEval xL yL := by
      rw [WeierstrassCurve.Affine.map_polynomial]
      rfl
    rw [h1]
    exact laurent_equation V
  let lam0 : (Polynomial (Polynomial T) ⧸ Ideal.span {WeierstrassCurve.Affine.polynomial V.toAffine}) →+* LaurentSeries T :=
    Ideal.Quotient.lift _ ev (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, hev, mul_zero])
  have hfx : f (xOverZ V.toProjective) = Ideal.Quotient.mk _ (Polynomial.C Polynomial.X : Polynomial (Polynomial T)) := by
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this
  have hfy : f (yOverZ V.toProjective) = Ideal.Quotient.mk _ (Polynomial.X : Polynomial (Polynomial T)) := by
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one] at this
    exact this
  refine ⟨lam0.comp f, ?_, ?_, ?_⟩
  · intro t
    rw [RingHom.comp_apply, show f (cZ V t) = algebraMap T _ t from RingHom.congr_fun hcomp t,
      IsScalarTower.algebraMap_apply T (Polynomial (Polynomial T)), Ideal.Quotient.algebraMap_eq,
      Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show lam0 (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C t))) = _
    rw [Ideal.Quotient.lift_mk, hevCC]
  · rw [RingHom.comp_apply, hfx]
    show lam0 (Ideal.Quotient.mk _ _) = _
    rw [Ideal.Quotient.lift_mk, hevCX]
  · rw [RingHom.comp_apply, hfy]
    show lam0 (Ideal.Quotient.mk _ _) = _
    rw [Ideal.Quotient.lift_mk, hevX]

theorem laurentEmbedding_mul_formalW (lam : ZChartRing V.toProjective →+* LaurentSeries T)
    (hx : lam (xOverZ V.toProjective) = ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T))
    (hy : lam (yOverZ V.toProjective) = -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T))) :
    lam (xOverZ V.toProjective) * ofPS T V.formalW = ofPS T PowerSeries.X ∧
      lam (yOverZ V.toProjective) * ofPS T V.formalW = -1 := by
  have hFU : ofPS T V.formalW * ofPS T V.wUnitFactor = HahnSeries.single (1 : ℤ) (1 : T) ^ 3 := by
    rw [← map_mul, V.formalW_mul_wUnitFactor, map_pow, HahnSeries.ofPowerSeries_X]
  constructor
  · rw [hx, mul_comm, ← mul_assoc, hFU, single_neg_two, HahnSeries.ofPowerSeries_X]
    calc (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) ^ 3 * HahnSeries.single (-1 : ℤ) (1 : T) ^ 2
        = HahnSeries.single (1 : ℤ) (1 : T) * (HahnSeries.single (1 : ℤ) (1 : T) * HahnSeries.single (-1 : ℤ) (1 : T)) ^ 2 := by ring
      _ = HahnSeries.single (1 : ℤ) (1 : T) := by rw [single_one_mul_single_neg_one, one_pow, mul_one]
  · rw [hy, neg_mul, mul_comm, ← mul_assoc, hFU, single_one_pow_three_mul_single_neg_three]

theorem exists_laurentEmbedding (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦc : ∀ t, Φ (cY V t) = PowerSeries.C t) (hΦx : Φ (xOverY V.toProjective) = -PowerSeries.X)
    (hΦz : Φ (zOverY V.toProjective) = -V.formalW) :
    ∃ lam : ZChartRing V.toProjective →+* LaurentSeries T,
      (∀ t, lam (cZ V t) = HahnSeries.C t) ∧
      lam (xOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = ofPS T (Φ (xOverY V.toProjective)) ∧
      lam (yOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = 1 := by
  obtain ⟨lam, hc, hx, hy⟩ := exists_laurentEmbedding_core V
  obtain ⟨h1, h2⟩ := laurentEmbedding_mul_formalW V lam hx hy
  refine ⟨lam, hc, ?_, ?_⟩
  · rw [hΦz, hΦx, map_neg, map_neg, mul_neg, h1]
  · rw [hΦz, map_neg, mul_neg, h2, neg_neg]

theorem laurentEmbedding_unique (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦz : Φ (zOverY V.toProjective) = -V.formalW)
    (lam lam' : ZChartRing V.toProjective →+* LaurentSeries T)
    (hc : ∀ t, lam (cZ V t) = HahnSeries.C t)
    (hx : lam (xOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = ofPS T (Φ (xOverY V.toProjective)))
    (hy : lam (yOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = 1)
    (hc' : ∀ t, lam' (cZ V t) = HahnSeries.C t)
    (hx' : lam' (xOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = ofPS T (Φ (xOverY V.toProjective)))
    (hy' : lam' (yOverZ V.toProjective) * ofPS T (Φ (zOverY V.toProjective)) = 1) : lam = lam' := by

  have hunit : IsUnit (ofPS T (Φ (zOverY V.toProjective))) := by
    rw [hΦz, map_neg, IsUnit.neg_iff]
    refine isUnit_iff_exists_inv.mpr ⟨ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T), ?_⟩
    rw [← mul_assoc, ← map_mul, V.formalW_mul_wUnitFactor, map_pow, HahnSeries.ofPowerSeries_X,
      single_one_pow_three_mul_single_neg_three]
  apply zChart_ringHom_ext V
  · exact RingHom.ext fun t => (hc t).trans (hc' t).symm
  · exact hunit.mul_right_cancel (hx.trans hx'.symm)
  · exact hunit.mul_right_cancel (hy.trans hy'.symm)

end embed

section lead
variable (V : WeierstrassCurve T)

theorem coeff_ofPS_mul_single (g : PowerSeries T) (k n : ℤ) :
    (ofPS T g * HahnSeries.single k (1 : T)).coeff n =
      if n - k < 0 then 0 else PowerSeries.coeff (n - k).natAbs g := by
  rw [HahnSeries.coeff_mul_single, mul_one]
  exact PowerSeries.coeff_coe g (n - k)

theorem laurentEmbedding_lead (lam : ZChartRing V.toProjective →+* LaurentSeries T)
    (hx : lam (xOverZ V.toProjective) = ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T))
    (hy : lam (yOverZ V.toProjective) = -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T))) :
    (∀ n : ℤ, n < -2 → (lam (xOverZ V.toProjective)).coeff n = 0) ∧
      (lam (xOverZ V.toProjective)).coeff (-2) = 1 ∧
      (∀ n : ℤ, n < -3 → (lam (yOverZ V.toProjective)).coeff n = 0) ∧
      (lam (yOverZ V.toProjective)).coeff (-3) = -1 := by
  have h0 : PowerSeries.coeff 0 V.wUnitFactor = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact V.constantCoeff_wUnitFactor
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [hx, coeff_ofPS_mul_single, if_pos (by omega)]
  · rw [hx, coeff_ofPS_mul_single, if_neg (by norm_num)]
    norm_num
    exact V.constantCoeff_wUnitFactor
  · intro n hn
    rw [hy, HahnSeries.coeff_neg, coeff_ofPS_mul_single, if_pos (by omega), neg_zero]
  · rw [hy, HahnSeries.coeff_neg, coeff_ofPS_mul_single, if_neg (by norm_num)]
    norm_num
    exact V.constantCoeff_wUnitFactor

end lead

section extras
variable (V : WeierstrassCurve T)

theorem coeff_single_neg_mul_ofPS (k : ℕ) (γ : PowerSeries T) :
    (∀ n : ℤ, n < -(k : ℤ) → (HahnSeries.single (-(k : ℤ)) (1 : T) * ofPS T γ).coeff n = 0) ∧
      (HahnSeries.single (-(k : ℤ)) (1 : T) * ofPS T γ).coeff (-(k : ℤ)) = PowerSeries.constantCoeff γ := by
  constructor
  · intro n hn
    rw [mul_comm, coeff_ofPS_mul_single, if_pos (by omega)]
  · rw [mul_comm, coeff_ofPS_mul_single, if_neg (by omega), ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    congr 1
    simp

theorem isUnit_ofPS_X : IsUnit (ofPS T PowerSeries.X) := by
  rw [HahnSeries.ofPowerSeries_X]
  exact isUnit_iff_exists_inv.mpr ⟨HahnSeries.single (-1 : ℤ) (1 : T), single_one_mul_single_neg_one⟩

theorem isUnit_ofPS_of_isUnit {f : PowerSeries T} (hf : IsUnit f) : IsUnit (ofPS T f) := hf.map _

theorem exists_ringEquiv_zChartRing_coordinateRing :
    ∃ e : ZChartRing V.toProjective ≃+* (Polynomial (Polynomial T) ⧸ Ideal.span {WeierstrassCurve.Affine.polynomial V.toAffine}),
      (∀ t, e (cZ V t) = Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C t))) ∧
      e (xOverZ V.toProjective) = Ideal.Quotient.mk _ (Polynomial.C Polynomial.X : Polynomial (Polynomial T)) ∧
      e (yOverZ V.toProjective) = Ideal.Quotient.mk _ (Polynomial.X : Polynomial (Polynomial T)) := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V.toProjective
  refine ⟨RingEquiv.ofBijective f hbij, ?_, ?_, ?_⟩
  · intro t
    show f (cZ V t) = _
    rw [show f (cZ V t) = algebraMap T _ t from RingHom.congr_fun hcomp t,
      IsScalarTower.algebraMap_apply T (Polynomial (Polynomial T)), Ideal.Quotient.algebraMap_eq,
      Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  · show f _ = _
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this
  · show f _ = _
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one] at this
    exact this

end extras

section filtration
variable (V : WeierstrassCurve T)

open _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

theorem single_mul_eval₂_xL (u : PowerSeries T) (hu : PowerSeries.constantCoeff u = 1) (p : Polynomial T) (d : ℕ)
    (hd : p.natDegree ≤ d) :
    ∃ G : PowerSeries T,
      HahnSeries.single ((2 * d : ℕ) : ℤ) (1 : T) *
          Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T u * HahnSeries.single (-2 : ℤ) (1 : T)) p
        = ofPS T G ∧ PowerSeries.constantCoeff G = p.coeff d := by
  classical
  refine ⟨∑ i ∈ Finset.range (d + 1), PowerSeries.C (p.coeff i) * u ^ i * PowerSeries.X ^ (2 * (d - i)), ?_, ?_⟩
  · rw [Polynomial.eval₂_eq_sum, Polynomial.sum_over_range' _ _ (d + 1) (by omega), Finset.mul_sum, map_sum]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hid : i ≤ d := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
      rw [map_mul, map_mul, map_pow, map_pow, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X, mul_pow,
        single_neg_two, ← pow_mul]

      have hZ : (HahnSeries.single ((2 * d : ℕ) : ℤ) (1 : T) : LaurentSeries T)
          = HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * (d - i)) * HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * i) := by
        rw [← pow_add, HahnSeries.single_pow, one_pow]
        congr 1
        have : 2 * (d - i) + 2 * i = 2 * d := by omega
        rw [this]
        simp
      rw [hZ]
      have hpm : (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) ^ (2 * i) * HahnSeries.single (-1 : ℤ) (1 : T) ^ (2 * i) = 1 := by
        rw [← mul_pow, single_one_mul_single_neg_one, one_pow]
      calc HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * (d - i)) * HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * i)
            * (HahnSeries.C (p.coeff i) * ((ofPS T u) ^ i * HahnSeries.single (-1 : ℤ) (1 : T) ^ (2 * i)))
          = HahnSeries.C (p.coeff i) * (ofPS T u) ^ i * HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * (d - i))
            * (HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * i) * HahnSeries.single (-1 : ℤ) (1 : T) ^ (2 * i)) := by ring
        _ = HahnSeries.C (p.coeff i) * (ofPS T u) ^ i * HahnSeries.single (1 : ℤ) (1 : T) ^ (2 * (d - i)) := by
          rw [hpm, mul_one]
    · intro n; simp
  · rw [map_sum]
    rw [Finset.sum_eq_single d]
    · simp [hu]
    · intro i hi hne
      have hid : i < d := lt_of_le_of_ne (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi) hne
      have : 2 * (d - i) ≠ 0 := by omega
      simp [this]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self d)) h

theorem coeff_neg_of_single_mul_eq_ofPS {N : ℕ} {f : LaurentSeries T} {G : PowerSeries T}
    (h : HahnSeries.single (N : ℤ) (1 : T) * f = ofPS T G) : f.coeff (-(N : ℤ)) = PowerSeries.constantCoeff G := by
  have := congrArg (fun g : LaurentSeries T => g.coeff 0) h
  rw [show (0 : ℤ) = -(N : ℤ) + N by ring, HahnSeries.coeff_single_mul_add, one_mul] at this
  rw [this, show -(N : ℤ) + N = ((0 : ℕ) : ℤ) by simp, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

end filtration

section filtration2
variable (V : WeierstrassCurve T)

theorem single_mul_eval₂_xL_mul_yL (u : PowerSeries T) (hu : PowerSeries.constantCoeff u = 1) (q : Polynomial T) (d : ℕ)
    (hd : q.natDegree ≤ d) :
    ∃ G : PowerSeries T,
      HahnSeries.single ((2 * d + 3 : ℕ) : ℤ) (1 : T) *
          (Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T u * HahnSeries.single (-2 : ℤ) (1 : T)) q
            * -(ofPS T u * HahnSeries.single (-3 : ℤ) (1 : T)))
        = ofPS T G ∧ PowerSeries.constantCoeff G = -q.coeff d := by
  obtain ⟨G, hG, hG0⟩ := single_mul_eval₂_xL u hu q d hd
  refine ⟨-(G * u), ?_, by rw [map_neg, map_mul, hG0, hu, mul_one]⟩
  have hsplit : (HahnSeries.single ((2 * d + 3 : ℕ) : ℤ) (1 : T) : LaurentSeries T)
      = HahnSeries.single ((2 * d : ℕ) : ℤ) (1 : T) * HahnSeries.single (3 : ℤ) (1 : T) := by
    rw [HahnSeries.single_mul_single, mul_one]
    norm_num
  have h33 : (HahnSeries.single (3 : ℤ) (1 : T) : LaurentSeries T) * HahnSeries.single (-3 : ℤ) (1 : T) = 1 := by
    rw [HahnSeries.single_mul_single, mul_one]; norm_num
  rw [hsplit, map_neg, map_mul, ← hG]
  calc HahnSeries.single ((2 * d : ℕ) : ℤ) (1 : T) * HahnSeries.single (3 : ℤ) (1 : T)
        * (Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T u * HahnSeries.single (-2 : ℤ) (1 : T)) q
          * -(ofPS T u * HahnSeries.single (-3 : ℤ) (1 : T)))
      = -(HahnSeries.single ((2 * d : ℕ) : ℤ) (1 : T)
          * Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T u * HahnSeries.single (-2 : ℤ) (1 : T)) q
          * ofPS T u * (HahnSeries.single (3 : ℤ) (1 : T) * HahnSeries.single (-3 : ℤ) (1 : T))) := by ring
    _ = _ := by rw [h33, mul_one]

theorem laurentEmbedding_normalForm (lam : ZChartRing V.toProjective →+* LaurentSeries T)
    (hc : ∀ t, lam (cZ V t) = HahnSeries.C t)
    (hx : lam (xOverZ V.toProjective) = ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T))
    (hy : lam (yOverZ V.toProjective) = -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T)))
    (a : ZChartRing V.toProjective) :
    ∃ p q : Polynomial T,
      a = Polynomial.eval₂ (cZ V) (xOverZ V.toProjective) p + Polynomial.eval₂ (cZ V) (xOverZ V.toProjective) q * yOverZ V.toProjective ∧
      lam a = Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T)) p
        + Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T)) q
          * -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T)) := by
  classical
  obtain ⟨e, hec, hex, hey⟩ := exists_ringEquiv_zChartRing_coordinateRing V

  let evB : Polynomial (Polynomial T) →+* ZChartRing V.toProjective :=
    Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (cZ V) (xOverZ V.toProjective)) (yOverZ V.toProjective)
  have hfacB : e.symm.toRingHom.comp (Ideal.Quotient.mk _) = evB := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · refine RingHom.ext fun t => ?_
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, evB, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_C]
        apply e.injective; rw [RingEquiv.apply_symm_apply]; exact (hec t).symm
      · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, evB, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_C, Polynomial.eval₂_X]
        apply e.injective; rw [RingEquiv.apply_symm_apply, hex]
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, evB, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X]
      apply e.injective; rw [RingEquiv.apply_symm_apply, hey]
  obtain ⟨p, q, hpq⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq (W' := V.toAffine) (e a)
  have hpq' : e a = Ideal.Quotient.mk _ (Polynomial.C p + Polynomial.C q * Polynomial.X) := by
    rw [← hpq, WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul, mul_one,
      map_add, map_mul]
    rfl
  have ha : a = evB (Polynomial.C p + Polynomial.C q * Polynomial.X) := by
    rw [← hfacB, RingHom.comp_apply, ← hpq']
    simp
  refine ⟨p, q, ?_, ?_⟩
  · rw [ha]
    simp only [evB, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X]
  · rw [ha]
    simp only [evB, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, map_add, map_mul, hy]
    congr 2 <;> rw [Polynomial.hom_eval₂, hx] <;> congr 1 <;> exact RingHom.ext hc

end filtration2

section filtration3
variable (V : WeierstrassCurve T)

theorem coeff_of_single_mul_eq_ofPS {K : ℕ} {f : LaurentSeries T} {G : PowerSeries T}
    (h : HahnSeries.single (K : ℤ) (1 : T) * f = ofPS T G) :
    (∀ n : ℤ, n < -(K : ℤ) → f.coeff n = 0) ∧ f.coeff (-(K : ℤ)) = PowerSeries.constantCoeff G := by
  have hf : f = HahnSeries.single (-(K : ℤ)) (1 : T) * ofPS T G := by
    rw [← h, ← mul_assoc, HahnSeries.single_mul_single, mul_one, neg_add_cancel, HahnSeries.single_zero_one, one_mul]
  rw [hf]
  exact coeff_single_neg_mul_ofPS K G

abbrev Ex (u : PowerSeries T) (p : Polynomial T) : LaurentSeries T :=
  Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T) (ofPS T u * HahnSeries.single (-2 : ℤ) (1 : T)) p

abbrev yLs (u : PowerSeries T) : LaurentSeries T := -(ofPS T u * HahnSeries.single (-3 : ℤ) (1 : T))

theorem single_nat_eq_ofPS_X_pow (k : ℕ) :
    (HahnSeries.single (k : ℤ) (1 : T) : LaurentSeries T) = ofPS T (PowerSeries.X ^ k) := by
  rw [map_pow, HahnSeries.ofPowerSeries_X, HahnSeries.single_pow, one_pow]; simp

theorem coeff_even (u : PowerSeries T) (hu : PowerSeries.constantCoeff u = 1) (p q : Polynomial T) (m : ℕ)
    (hp : p.natDegree ≤ m) (hq : q = 0 ∨ q.natDegree + 2 ≤ m) :
    (Ex u p + Ex u q * yLs u).coeff (-((2 * m : ℕ) : ℤ)) = p.coeff m := by
  obtain ⟨Gp, hGp, hGp0⟩ := single_mul_eval₂_xL u hu p m hp
  rw [HahnSeries.coeff_add, (coeff_of_single_mul_eq_ofPS hGp).2, hGp0]
  rcases hq with rfl | hq
  · simp
  · obtain ⟨Gq, hGq, -⟩ := single_mul_eval₂_xL_mul_yL u hu q (m - 2) (by omega)
    have hvan := (coeff_of_single_mul_eq_ofPS hGq).1 (-((2 * m : ℕ) : ℤ)) (by push_cast; omega)
    rw [hvan, add_zero]

theorem coeff_odd (u : PowerSeries T) (hu : PowerSeries.constantCoeff u = 1) (p q : Polynomial T) (m : ℕ)
    (hp : p.natDegree ≤ m + 1) (hq : q.natDegree ≤ m) :
    (Ex u p + Ex u q * yLs u).coeff (-((2 * m + 3 : ℕ) : ℤ)) = -q.coeff m := by
  obtain ⟨Gq, hGq, hGq0⟩ := single_mul_eval₂_xL_mul_yL u hu q m hq
  obtain ⟨Gp, hGp, -⟩ := single_mul_eval₂_xL u hu p (m + 2) (by omega)
  rw [HahnSeries.coeff_add, (coeff_of_single_mul_eq_ofPS hGq).2, hGq0]

  obtain ⟨Gp', hGp', -⟩ := single_mul_eval₂_xL u hu p (m + 1) hp
  have h' : HahnSeries.single ((2 * m + 3 : ℕ) : ℤ) (1 : T) * (Ex u p) = ofPS T (PowerSeries.X * Gp') := by
    have hs : (HahnSeries.single ((2 * m + 3 : ℕ) : ℤ) (1 : T) : LaurentSeries T)
        = HahnSeries.single (1 : ℤ) (1 : T) * HahnSeries.single ((2 * (m + 1) : ℕ) : ℤ) (1 : T) := by
      rw [HahnSeries.single_mul_single, one_mul]; norm_num; ring
    rw [hs, mul_assoc, hGp', map_mul, HahnSeries.ofPowerSeries_X]
  rw [(coeff_of_single_mul_eq_ofPS h').2, map_mul, PowerSeries.constantCoeff_X, zero_mul, zero_add]

theorem laurentEmbedding_filtration (lam : ZChartRing V.toProjective →+* LaurentSeries T)
    (hc : ∀ t, lam (cZ V t) = HahnSeries.C t)
    (hx : lam (xOverZ V.toProjective) = ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T))
    (hy : lam (yOverZ V.toProjective) = -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T))) :
    (∀ a : ZChartRing V.toProjective, (∀ n : ℤ, n < -2 → (lam a).coeff n = 0) →
      ∃ c₀ c₁ : T, a = cZ V c₁ * xOverZ V.toProjective + cZ V c₀ ∧ c₁ = (lam a).coeff (-2)) ∧
    (∀ a : ZChartRing V.toProjective, (∀ n : ℤ, n < -3 → (lam a).coeff n = 0) →
      ∃ c₀ c₁ c₂ : T, a = cZ V c₂ * yOverZ V.toProjective + cZ V c₁ * xOverZ V.toProjective + cZ V c₀ ∧
        c₂ = -((lam a).coeff (-3))) := by
  classical
  have hu := V.constantCoeff_wUnitFactor

  have keyq : ∀ (p q : Polynomial T) (M : ℕ), (∀ n : ℤ, n < -(M : ℤ) → (Ex V.wUnitFactor p + Ex V.wUnitFactor q * yLs V.wUnitFactor).coeff n = 0) →
      q ≠ 0 → 2 * q.natDegree + 3 ≤ M := by
    intro p q M hvan hq0
    by_contra hlt
    push Not at hlt
    by_cases hpq : p.natDegree ≤ q.natDegree + 1
    · have h := coeff_odd V.wUnitFactor hu p q q.natDegree hpq le_rfl
      rw [hvan _ (by push_cast; omega), Polynomial.coeff_natDegree] at h
      exact hq0 (Polynomial.leadingCoeff_eq_zero.mp (neg_eq_zero.mp h.symm))
    · push Not at hpq
      have hp0 : p ≠ 0 := by rintro rfl; simp at hpq
      have h := coeff_even V.wUnitFactor hu p q p.natDegree le_rfl (Or.inr (by omega))
      rw [hvan _ (by push_cast; omega), Polynomial.coeff_natDegree] at h
      exact hp0 (Polynomial.leadingCoeff_eq_zero.mp h.symm)
  have keyp : ∀ (p q : Polynomial T) (M : ℕ), (∀ n : ℤ, n < -(M : ℤ) → (Ex V.wUnitFactor p + Ex V.wUnitFactor q * yLs V.wUnitFactor).coeff n = 0) →
      (q = 0 ∨ q.natDegree + 2 ≤ 2) → M < 4 → p.natDegree ≤ 1 := by
    intro p q M hvan hq hM
    by_contra hlt
    push Not at hlt
    have hp0 : p ≠ 0 := by rintro rfl; simp at hlt
    have hq' : q = 0 ∨ q.natDegree + 2 ≤ p.natDegree := hq.imp id (fun h => by omega)
    have h := coeff_even V.wUnitFactor hu p q p.natDegree le_rfl hq'
    rw [hvan _ (by push_cast; omega), Polynomial.coeff_natDegree] at h
    exact hp0 (Polynomial.leadingCoeff_eq_zero.mp h.symm)
  constructor
  · intro a hvan
    obtain ⟨p, q, ha, hla⟩ := laurentEmbedding_normalForm V lam hc hx hy a
    rw [hla] at hvan
    have hq : q = 0 := by
      by_contra hq0
      have := keyq p q 2 (by exact_mod_cast hvan) hq0
      omega
    subst hq
    have hp : p.natDegree ≤ 1 := keyp p 0 2 (by exact_mod_cast hvan) (Or.inl rfl) (by norm_num)
    have hpeq := Polynomial.eq_X_add_C_of_natDegree_le_one hp
    refine ⟨p.coeff 0, p.coeff 1, ?_, ?_⟩
    · rw [ha, hpeq]
      simp [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
    · have h := coeff_even V.wUnitFactor hu p 0 1 hp (Or.inl rfl)
      rw [hla]
      exact_mod_cast h.symm
  · intro a hvan
    obtain ⟨p, q, ha, hla⟩ := laurentEmbedding_normalForm V lam hc hx hy a
    rw [hla] at hvan
    have hq : q.natDegree = 0 := by
      by_cases hq0 : q = 0
      · rw [hq0, Polynomial.natDegree_zero]
      · have := keyq p q 3 (by exact_mod_cast hvan) hq0
        omega
    have hp : p.natDegree ≤ 1 := keyp p q 3 (by exact_mod_cast hvan) (Or.inr (by omega)) (by norm_num)
    have hpeq := Polynomial.eq_X_add_C_of_natDegree_le_one hp
    have hqeq := Polynomial.eq_C_of_natDegree_eq_zero hq
    refine ⟨p.coeff 0, p.coeff 1, q.coeff 0, ?_, ?_⟩
    · rw [ha, hpeq, hqeq]
      simp [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
      ring_nf
    · have h := coeff_odd V.wUnitFactor hu p q 0 (by omega) (by omega)
      rw [hla]
      have h2 : (Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T)
            (ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T)) p
          + Polynomial.eval₂ (HahnSeries.C : T →+* LaurentSeries T)
            (ofPS T V.wUnitFactor * HahnSeries.single (-2 : ℤ) (1 : T)) q
            * -(ofPS T V.wUnitFactor * HahnSeries.single (-3 : ℤ) (1 : T))).coeff (-3) = -q.coeff 0 := by
        simpa using h
      rw [h2, neg_neg]

end filtration3

end WMLocal

end

theorem solution
    (T : Type) [CommRing T] (V : WeierstrassCurve T)
    (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY V.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY V.toProjective) = - V.formalW) :
    ∃ lam : ZChartRing V.toProjective →+* LaurentSeries T,
      (∀ t : T, lam (fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) t)) =
        HahnSeries.C t) ∧
      lam (xOverZ V.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V.toProjective)) =
        HahnSeries.ofPowerSeries ℤ T (Φ (xOverY V.toProjective)) ∧
      lam (yOverZ V.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V.toProjective)) = 1 ∧
      (∀ a : ZChartRing V.toProjective, (∀ n : ℤ, n < -2 → (lam a).coeff n = 0) →
        ∃ c₀ c₁ : T, a = fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₁) *
            xOverZ V.toProjective +
          fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₀) ∧
          c₁ = (lam a).coeff (-2)) ∧
      (∀ a : ZChartRing V.toProjective, (∀ n : ℤ, n < -3 → (lam a).coeff n = 0) →
        ∃ c₀ c₁ c₂ : T, a = fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₂) *
            yOverZ V.toProjective +
          fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₁) *
            xOverZ V.toProjective +
          fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₀) ∧
          c₂ = -((lam a).coeff (-3))) := by
  obtain ⟨lam, hc, hx, hy⟩ := WMLocal.exists_laurentEmbedding_core V
  obtain ⟨h1, h2⟩ := WMLocal.laurentEmbedding_mul_formalW V lam hx hy
  obtain ⟨hF2, hF3⟩ := WMLocal.laurentEmbedding_filtration V lam hc hx hy
  refine ⟨lam, hc, ?_, ?_, hF2, hF3⟩
  · rw [hΦz, hΦx, map_neg, map_neg, mul_neg, h1]
  · rw [hΦz, map_neg, mul_neg, h2, neg_neg]

end S_WeierstrassProjModel_exists_laurent_zChartRing_filtration
end P2MW
export P2MW.S_WeierstrassProjModel_exists_laurent_zChartRing_filtration (solution)
