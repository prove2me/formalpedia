-- Prove2me | solution 1 for WeierstrassCurve.reducePoint_some_add_some_of_not_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a24009c7-2af2-561f-b686-cb2fad753f2f

import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Definitions.Def_EllipticCurve_PointReduction
import Theorems.Thm_WeierstrassCurve_exists_valuation_eq_exp_of_not_le_one
import Theorems.Thm_WeierstrassCurve_valuation_le_one_of_equation
import Theorems.Thm_WeierstrassCurve_reducePoint_some
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_reducePoint_some_add_some_of_not_le_one

set_option autoImplicit false

open WeierstrassCurve IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum
p2m_open "IsLocalRing~maximalIdeal"
open scoped WeierstrassCurve.Affine

namespace Deep

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable (R) (W : WeierstrassCurve K)

theorem exists_algebraMap_eq_of_valuation_le_one {x : K}
    (hx : valuation K (maximalIdeal R) x ≤ 1) : ∃ r : R, algebraMap R K r = x :=
  exists_lift_of_le_one hx

theorem valuation_dichotomy [W.IsIntegral R] {x y : K} (h : W.toAffine.Equation x y)
    (hx : ¬ valuation K (maximalIdeal R) x ≤ 1) :
    ∃ s : ℕ, 0 < s ∧
      valuation K (maximalIdeal R) x = WithZero.exp (2 * (s : ℤ)) ∧
      valuation K (maximalIdeal R) y = WithZero.exp (3 * (s : ℤ)) :=
  WeierstrassCurve.exists_valuation_eq_exp_of_not_le_one R W h hx

variable [W.HasGoodReduction R]

private theorem _root_.Deep.reducePoint_some {x y : K} (h : W.toAffine.Nonsingular x y)
    (hx : valuation K (maximalIdeal R) x ≤ 1) (hy : valuation K (maximalIdeal R) y ≤ 1) :
    ∃ h', reducePoint_alt R W (.some x y h) = .some (reduceCoord R x) (reduceCoord R y) h' :=
  WeierstrassCurve.reducePoint_some R W h hx hy

p2m_export "Deep" "reducePoint_some"

theorem valuation_y_le_one {x y : K} (hE : W.toAffine.Equation x y)
    (hx : valuation K (maximalIdeal R) x ≤ 1) :
    valuation K (maximalIdeal R) y ≤ 1 :=
  WeierstrassCurve.valuation_le_one_of_equation R W hE hx

theorem reduceCoord_algebraMap (r : R) :
    reduceCoord R (algebraMap R K r) = residue R r := by
  have hex : ∃ r' : R, algebraMap R K r' = algebraMap R K r := ⟨r, rfl⟩
  rw [reduceCoord, dif_pos hex]
  exact congrArg _ (IsFractionRing.injective R K hex.choose_spec)

theorem reduceCoord_eq_zero_iff_lt {x : K}
    (hx : valuation K (maximalIdeal R) x ≤ 1) :
    reduceCoord R x = 0 ↔ valuation K (maximalIdeal R) x < 1 := by
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_valuation_le_one R hx
  rw [← hr, reduceCoord_algebraMap, residue_eq_zero_iff]
  exact (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) r).symm

theorem reduction_a₁ : (reduction R W).a₁ = residue R (integralModel R W).a₁ := by
  simp only [reduction, map_a₁]

theorem reduction_a₂ : (reduction R W).a₂ = residue R (integralModel R W).a₂ := by
  simp only [reduction, map_a₂]

theorem reduction_a₃ : (reduction R W).a₃ = residue R (integralModel R W).a₃ := by
  simp only [reduction, map_a₃]

theorem reduction_a₄ : (reduction R W).a₄ = residue R (integralModel R W).a₄ := by
  simp only [reduction, map_a₄]

theorem reduction_a₆ : (reduction R W).a₆ = residue R (integralModel R W).a₆ := by
  simp only [reduction, map_a₆]

theorem equation_lift {x y : K} (h : W.toAffine.Equation x y) {rx ry : R}
    (hrx : algebraMap R K rx = x) (hry : algebraMap R K ry = y) :
    (integralModel R W).toAffine.Equation rx ry := by
  have heqK : ((integralModel R W).map (algebraMap R K)).toAffine.Equation
      (algebraMap R K rx) (algebraMap R K ry) := by
    have hbc : (integralModel R W).map (algebraMap R K) = W := baseChange_integralModel_eq R W
    rw [hbc, hrx, hry]
    exact h
  exact (Affine.map_equation _ (IsFractionRing.injective R K) _ _).mp heqK

theorem reduced_nonsingular {rx ry : R} (h : (integralModel R W).toAffine.Equation rx ry) :
    (reduction R W).toAffine.Nonsingular (residue R rx) (residue R ry) := by
  haveI hell : (reduction R W).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).mp ‹W.HasGoodReduction R›
  have heqk : (reduction R W).toAffine.Equation (residue R rx) (residue R ry) :=
    h.map (residue R)
  exact Affine.equation_iff_nonsingular.mp heqk

theorem slope_identity {x₁ y₁ x₂ y₂ : K} (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) :
    (y₁ - y₂) * (y₁ + y₂ + W.a₁ * x₁ + W.a₃)
      = (x₁ - x₂) * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂) := by
  rw [Affine.equation_iff] at h₁ h₂
  linear_combination h₁ - h₂

theorem valuation_a₁_le_one : valuation K (maximalIdeal R) W.a₁ ≤ 1 := by
  rw [← integralModel_a₁_eq R W]; exact valuation_le_one (maximalIdeal R) _

theorem valuation_a₂_le_one : valuation K (maximalIdeal R) W.a₂ ≤ 1 := by
  rw [← integralModel_a₂_eq R W]; exact valuation_le_one (maximalIdeal R) _

theorem valuation_a₃_le_one : valuation K (maximalIdeal R) W.a₃ ≤ 1 := by
  rw [← integralModel_a₃_eq R W]; exact valuation_le_one (maximalIdeal R) _

theorem valuation_a₄_le_one : valuation K (maximalIdeal R) W.a₄ ≤ 1 := by
  rw [← integralModel_a₄_eq R W]; exact valuation_le_one (maximalIdeal R) _

theorem valuation_a₆_le_one : valuation K (maximalIdeal R) W.a₆ ≤ 1 := by
  rw [← integralModel_a₆_eq R W]; exact valuation_le_one (maximalIdeal R) _

theorem le_exp_sub {a b : ℤ} {A : WithZero (Multiplicative ℤ)}
    (h : WithZero.exp a * A ≤ WithZero.exp b) : A ≤ WithZero.exp (b - a) := by
  have h2 := mul_le_mul_right h (WithZero.exp (-a))
  rw [← mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, one_mul,
    ← WithZero.exp_add] at h2
  rw [show (b - a : ℤ) = -a + b by omega]
  exact h2

theorem reducePoint_add_int_pole [DecidableEq K] [DecidableEq (ResidueField R)]
    {x₁ y₁ x₂ y₂ : K} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx₁ : valuation K (maximalIdeal R) x₁ ≤ 1) (hx₂ : ¬ valuation K (maximalIdeal R) x₂ ≤ 1) :
    reducePoint_alt R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = reducePoint_alt R W (.some x₁ y₁ h₁) := by
  obtain ⟨s, hs, hvx₂, hvy₂⟩ := valuation_dichotomy R W h₂.1 hx₂
  have hy₁ : valuation K (maximalIdeal R) y₁ ≤ 1 := valuation_y_le_one R W h₁.1 hx₁
  have hxne : x₁ ≠ x₂ := fun h => hx₂ (h ▸ hx₁)
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := fun hc => hxne hc.1
  rw [Affine.Point.add_some hxy]

  have h1lt2s : (1 : WithZero (Multiplicative ℤ)) < WithZero.exp (2 * (s : ℤ)) := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by omega)
  have h1lt3s : (1 : WithZero (Multiplicative ℤ)) < WithZero.exp (3 * (s : ℤ)) := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by omega)
  have hnegs1 : WithZero.exp (-(s : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by omega)

  have hvdx : valuation K (maximalIdeal R) (x₁ - x₂) = WithZero.exp (2 * (s : ℤ)) := by
    rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _
      (by rw [Valuation.map_neg, hvx₂]; exact lt_of_le_of_lt hx₁ h1lt2s),
      Valuation.map_neg, hvx₂]
  have hvdy : valuation K (maximalIdeal R) (y₁ - y₂) = WithZero.exp (3 * (s : ℤ)) := by
    rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _
      (by rw [Valuation.map_neg, hvy₂]; exact lt_of_le_of_lt hy₁ h1lt3s),
      Valuation.map_neg, hvy₂]
  have hpow2 : valuation K (maximalIdeal R) ((x₁ - x₂) ^ 2)
      = WithZero.exp (4 * (s : ℤ)) := by
    rw [map_pow, hvdx, ← WithZero.exp_nsmul, nsmul_eq_mul]
    congr 1
    push_cast
    ring
  have hpow3 : valuation K (maximalIdeal R) ((x₁ - x₂) ^ 3)
      = WithZero.exp (6 * (s : ℤ)) := by
    rw [map_pow, hvdx, ← WithZero.exp_nsmul, nsmul_eq_mul]
    congr 1
    push_cast
    ring

  have hℓx : W.toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
    rw [Affine.slope_of_X_ne hxne, div_mul_cancel₀ _ (sub_ne_zero.mpr hxne)]

  have e₁ := h₁.1
  have e₂ := h₂.1
  rw [Affine.equation_iff] at e₁ e₂

  obtain ⟨r1x, h1x⟩ := exists_algebraMap_eq_of_valuation_le_one R hx₁
  obtain ⟨r1y, h1y⟩ := exists_algebraMap_eq_of_valuation_le_one R hy₁
  have hAK : -x₁ ^ 3 + W.toAffine.a₄ * x₁ + 2 * W.toAffine.a₆ + -(W.toAffine.a₃ * y₁)
      = algebraMap R K (-r1x ^ 3 + (integralModel R W).a₄ * r1x
          + 2 * (integralModel R W).a₆ + -((integralModel R W).a₃ * r1y)) := by
    simp only [map_add, map_neg, map_mul, map_pow, map_ofNat, h1x, h1y,
      integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq]
  have hvA : valuation K (maximalIdeal R)
      (-x₁ ^ 3 + W.toAffine.a₄ * x₁ + 2 * W.toAffine.a₆ + -(W.toAffine.a₃ * y₁)) ≤ 1 := by
    rw [hAK]; exact valuation_le_one _ _
  have hnK : 3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁
      = algebraMap R K (3 * r1x ^ 2 + 2 * (integralModel R W).a₂ * r1x
          + (integralModel R W).a₄ - (integralModel R W).a₁ * r1y) := by
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, h1x, h1y,
      integralModel_a₁_eq, integralModel_a₂_eq, integralModel_a₄_eq]
  have hvn : valuation K (maximalIdeal R)
      (3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁) ≤ 1 := by
    rw [hnK]; exact valuation_le_one _ _
  have hdK : 2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃
      = algebraMap R K (2 * r1y + (integralModel R W).a₁ * r1x
          + (integralModel R W).a₃) := by
    simp only [map_add, map_mul, map_ofNat, h1x, h1y,
      integralModel_a₁_eq, integralModel_a₃_eq]
  have hvd : valuation K (maximalIdeal R)
      (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃) ≤ 1 := by
    rw [hdK]; exact valuation_le_one _ _

  have hM : (x₁ - x₂) ^ 2
        * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁)
      = (-x₁ ^ 3 + W.toAffine.a₄ * x₁ + 2 * W.toAffine.a₆ + -(W.toAffine.a₃ * y₁))
        + (3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁) * x₂
        + -((2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃) * y₂) := by
    have hexp : (x₁ - x₂) ^ 2
          * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁)
        = (W.toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂)) ^ 2
          + W.toAffine.a₁ * (W.toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂)) * (x₁ - x₂)
          - (W.toAffine.a₂ + 2 * x₁ + x₂) * (x₁ - x₂) ^ 2 := by
      simp only [Affine.addX]
      ring
    rw [hexp, hℓx]
    linear_combination e₁ + e₂

  have hvM : valuation K (maximalIdeal R)
      ((-x₁ ^ 3 + W.toAffine.a₄ * x₁ + 2 * W.toAffine.a₆ + -(W.toAffine.a₃ * y₁))
        + (3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁) * x₂
        + -((2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃) * y₂))
      ≤ WithZero.exp (3 * (s : ℤ)) := by
    refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
    · exact le_trans hvA (le_of_lt h1lt3s)
    · rw [map_mul]
      calc valuation K (maximalIdeal R)
            (3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁)
            * valuation K (maximalIdeal R) x₂
          ≤ 1 * WithZero.exp (2 * (s : ℤ)) := mul_le_mul' hvn (le_of_eq hvx₂)
        _ = WithZero.exp (2 * (s : ℤ)) := one_mul _
        _ ≤ WithZero.exp (3 * (s : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
    · rw [Valuation.map_neg, map_mul]
      calc valuation K (maximalIdeal R) (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃)
            * valuation K (maximalIdeal R) y₂
          ≤ 1 * WithZero.exp (3 * (s : ℤ)) := mul_le_mul' hvd (le_of_eq hvy₂)
        _ = WithZero.exp (3 * (s : ℤ)) := one_mul _

  have hv31 : valuation K (maximalIdeal R)
      (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁)
      ≤ WithZero.exp (-(s : ℤ)) := by
    have h0 : WithZero.exp (4 * (s : ℤ))
        * valuation K (maximalIdeal R)
            (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁)
        ≤ WithZero.exp (3 * (s : ℤ)) := by
      rw [← hpow2, ← map_mul, hM]
      exact hvM
    have h1 := le_exp_sub h0
    rw [show (3 * (s : ℤ) - 4 * (s : ℤ)) = -(s : ℤ) by omega] at h1
    exact h1
  have hvx₃ : valuation K (maximalIdeal R)
      (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)) ≤ 1 := by
    rw [← sub_add_cancel (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)) x₁]
    exact Valuation.map_add_le _ (le_trans hv31 (le_of_lt hnegs1)) hx₁

  have hM₂ : (x₁ - x₂) ^ 3
        * (W.toAffine.slope x₁ x₂ y₁ y₂
            * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁)
          + (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃))
      = (-x₁ ^ 3 + W.toAffine.a₄ * x₁ + 2 * W.toAffine.a₆ + -(W.toAffine.a₃ * y₁))
          * (y₁ - y₂)
        + (3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁)
          * (x₂ * (y₁ - y₂))
        + -((2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃) * (y₁ * y₂))
        + (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃)
          * (W.toAffine.a₂ * x₂ ^ 2 + W.toAffine.a₄ * x₂ + W.toAffine.a₆
            + -(W.toAffine.a₁ * (x₂ * y₂)) + -(W.toAffine.a₃ * y₂))
        + (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃)
          * (x₁ ^ 3 + -(3 * (x₁ ^ 2 * x₂)) + 3 * (x₁ * x₂ ^ 2)) := by
    have h0 : (x₁ - x₂) ^ 3
          * (W.toAffine.slope x₁ x₂ y₁ y₂
              * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁)
            + (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃))
        = (W.toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂))
            * ((x₁ - x₂) ^ 2
              * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁))
          + (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃) * (x₁ - x₂) ^ 3 := by
      ring
    rw [h0, hℓx, hM]
    linear_combination (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃) * e₂

  have hvM₂ : valuation K (maximalIdeal R)
      ((-x₁ ^ 3 + W.toAffine.a₄ * x₁ + 2 * W.toAffine.a₆ + -(W.toAffine.a₃ * y₁))
          * (y₁ - y₂)
        + (3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁)
          * (x₂ * (y₁ - y₂))
        + -((2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃) * (y₁ * y₂))
        + (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃)
          * (W.toAffine.a₂ * x₂ ^ 2 + W.toAffine.a₄ * x₂ + W.toAffine.a₆
            + -(W.toAffine.a₁ * (x₂ * y₂)) + -(W.toAffine.a₃ * y₂))
        + (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃)
          * (x₁ ^ 3 + -(3 * (x₁ ^ 2 * x₂)) + 3 * (x₁ * x₂ ^ 2)))
      ≤ WithZero.exp (5 * (s : ℤ)) := by
    have hx₂2 : valuation K (maximalIdeal R) (x₂ ^ 2)
        = WithZero.exp (4 * (s : ℤ)) := by
      rw [map_pow, hvx₂, ← WithZero.exp_nsmul, nsmul_eq_mul]
      congr 1
      push_cast
      ring
    refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _
      (Valuation.map_add_le _ ?_ ?_) ?_) ?_) ?_
    ·
      rw [map_mul]
      calc valuation K (maximalIdeal R)
            (-x₁ ^ 3 + W.toAffine.a₄ * x₁ + 2 * W.toAffine.a₆ + -(W.toAffine.a₃ * y₁))
            * valuation K (maximalIdeal R) (y₁ - y₂)
          ≤ 1 * WithZero.exp (3 * (s : ℤ)) := mul_le_mul' hvA (le_of_eq hvdy)
        _ = WithZero.exp (3 * (s : ℤ)) := one_mul _
        _ ≤ WithZero.exp (5 * (s : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
    ·
      rw [map_mul, map_mul]
      calc valuation K (maximalIdeal R)
            (3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁)
            * (valuation K (maximalIdeal R) x₂ * valuation K (maximalIdeal R) (y₁ - y₂))
          ≤ 1 * (WithZero.exp (2 * (s : ℤ)) * WithZero.exp (3 * (s : ℤ))) :=
            mul_le_mul' hvn (mul_le_mul' (le_of_eq hvx₂) (le_of_eq hvdy))
        _ = WithZero.exp (5 * (s : ℤ)) := by
            rw [one_mul, ← WithZero.exp_add]
            congr 1
            ring
    ·
      rw [Valuation.map_neg, map_mul, map_mul]
      calc valuation K (maximalIdeal R) (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃)
            * (valuation K (maximalIdeal R) y₁ * valuation K (maximalIdeal R) y₂)
          ≤ 1 * (1 * WithZero.exp (3 * (s : ℤ))) :=
            mul_le_mul' hvd (mul_le_mul' hy₁ (le_of_eq hvy₂))
        _ = WithZero.exp (3 * (s : ℤ)) := by rw [one_mul, one_mul]
        _ ≤ WithZero.exp (5 * (s : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
    ·
      rw [map_mul]
      have hinner : valuation K (maximalIdeal R)
          (W.toAffine.a₂ * x₂ ^ 2 + W.toAffine.a₄ * x₂ + W.toAffine.a₆
            + -(W.toAffine.a₁ * (x₂ * y₂)) + -(W.toAffine.a₃ * y₂))
          ≤ WithZero.exp (5 * (s : ℤ)) := by
        refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _
          (Valuation.map_add_le _ ?_ ?_) ?_) ?_) ?_
        · rw [map_mul]
          calc valuation K (maximalIdeal R) W.toAffine.a₂
                * valuation K (maximalIdeal R) (x₂ ^ 2)
              ≤ 1 * WithZero.exp (4 * (s : ℤ)) :=
                mul_le_mul' (valuation_a₂_le_one R W) (le_of_eq hx₂2)
            _ = WithZero.exp (4 * (s : ℤ)) := one_mul _
            _ ≤ WithZero.exp (5 * (s : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
        · rw [map_mul]
          calc valuation K (maximalIdeal R) W.toAffine.a₄
                * valuation K (maximalIdeal R) x₂
              ≤ 1 * WithZero.exp (2 * (s : ℤ)) :=
                mul_le_mul' (valuation_a₄_le_one R W) (le_of_eq hvx₂)
            _ = WithZero.exp (2 * (s : ℤ)) := one_mul _
            _ ≤ WithZero.exp (5 * (s : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
        · exact le_trans (valuation_a₆_le_one R W)
            (le_of_lt (by rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by omega)))
        · rw [Valuation.map_neg, map_mul, map_mul]
          calc valuation K (maximalIdeal R) W.toAffine.a₁
                * (valuation K (maximalIdeal R) x₂ * valuation K (maximalIdeal R) y₂)
              ≤ 1 * (WithZero.exp (2 * (s : ℤ)) * WithZero.exp (3 * (s : ℤ))) :=
                mul_le_mul' (valuation_a₁_le_one R W)
                  (mul_le_mul' (le_of_eq hvx₂) (le_of_eq hvy₂))
            _ = WithZero.exp (5 * (s : ℤ)) := by
                rw [one_mul, ← WithZero.exp_add]
                congr 1
                ring
        · rw [Valuation.map_neg, map_mul]
          calc valuation K (maximalIdeal R) W.toAffine.a₃
                * valuation K (maximalIdeal R) y₂
              ≤ 1 * WithZero.exp (3 * (s : ℤ)) :=
                mul_le_mul' (valuation_a₃_le_one R W) (le_of_eq hvy₂)
            _ = WithZero.exp (3 * (s : ℤ)) := one_mul _
            _ ≤ WithZero.exp (5 * (s : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
      calc valuation K (maximalIdeal R) (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃)
            * valuation K (maximalIdeal R)
              (W.toAffine.a₂ * x₂ ^ 2 + W.toAffine.a₄ * x₂ + W.toAffine.a₆
                + -(W.toAffine.a₁ * (x₂ * y₂)) + -(W.toAffine.a₃ * y₂))
          ≤ 1 * WithZero.exp (5 * (s : ℤ)) := mul_le_mul' hvd hinner
        _ = WithZero.exp (5 * (s : ℤ)) := one_mul _
    ·
      rw [map_mul]
      have hinner : valuation K (maximalIdeal R)
          (x₁ ^ 3 + -(3 * (x₁ ^ 2 * x₂)) + 3 * (x₁ * x₂ ^ 2))
          ≤ WithZero.exp (4 * (s : ℤ)) := by
        have h3le : valuation K (maximalIdeal R) (3 : K) ≤ 1 := by
          rw [show ((3 : K)) = algebraMap R K 3 from (map_ofNat _ 3).symm]
          exact valuation_le_one _ _
        have hx₂2 : valuation K (maximalIdeal R) (x₂ ^ 2)
            = WithZero.exp (4 * (s : ℤ)) := by
          rw [map_pow, hvx₂, ← WithZero.exp_nsmul, nsmul_eq_mul]
          congr 1
          push_cast
          ring
        refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
        · rw [map_pow]
          exact le_trans (pow_le_one' hx₁ 3)
            (le_of_lt (by rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by omega)))
        · rw [Valuation.map_neg, map_mul, map_mul, map_pow]
          calc valuation K (maximalIdeal R) (3 : K)
                * (valuation K (maximalIdeal R) x₁ ^ 2 * valuation K (maximalIdeal R) x₂)
              ≤ 1 * (1 * WithZero.exp (2 * (s : ℤ))) :=
                mul_le_mul' h3le (mul_le_mul' (pow_le_one' hx₁ 2) (le_of_eq hvx₂))
            _ = WithZero.exp (2 * (s : ℤ)) := by rw [one_mul, one_mul]
            _ ≤ WithZero.exp (4 * (s : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
        · rw [map_mul, map_mul]
          calc valuation K (maximalIdeal R) (3 : K)
                * (valuation K (maximalIdeal R) x₁ * valuation K (maximalIdeal R) (x₂ ^ 2))
              ≤ 1 * (1 * WithZero.exp (4 * (s : ℤ))) :=
                mul_le_mul' h3le (mul_le_mul' hx₁ (le_of_eq hx₂2))
            _ = WithZero.exp (4 * (s : ℤ)) := by rw [one_mul, one_mul]
      calc valuation K (maximalIdeal R) (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃)
            * valuation K (maximalIdeal R)
              (x₁ ^ 3 + -(3 * (x₁ ^ 2 * x₂)) + 3 * (x₁ * x₂ ^ 2))
          ≤ 1 * WithZero.exp (4 * (s : ℤ)) := mul_le_mul' hvd hinner
        _ = WithZero.exp (4 * (s : ℤ)) := one_mul _
        _ ≤ WithZero.exp (5 * (s : ℤ)) := WithZero.exp_le_exp.mpr (by omega)

  have hvly : valuation K (maximalIdeal R)
      (W.toAffine.slope x₁ x₂ y₁ y₂
          * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁)
        + (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃))
      ≤ WithZero.exp (-(s : ℤ)) := by
    have h0 : WithZero.exp (6 * (s : ℤ))
        * valuation K (maximalIdeal R)
            (W.toAffine.slope x₁ x₂ y₁ y₂
                * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁)
              + (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃))
        ≤ WithZero.exp (5 * (s : ℤ)) := by
      rw [← hpow3, ← map_mul, hM₂]
      exact hvM₂
    have h1 := le_exp_sub h0
    rw [show (5 * (s : ℤ) - 6 * (s : ℤ)) = -(s : ℤ) by omega] at h1
    exact h1

  have hy₃eq : W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) - y₁
      = -(W.toAffine.slope x₁ x₂ y₁ y₂
            * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁)
          + (2 * y₁ + W.toAffine.a₁ * x₁ + W.toAffine.a₃))
        + -(W.toAffine.a₁
            * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁)) := by
    simp only [Affine.addY, Affine.negAddY, Affine.negY]
    ring
  have hvy₃1 : valuation K (maximalIdeal R)
      (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) - y₁)
      ≤ WithZero.exp (-(s : ℤ)) := by
    rw [hy₃eq]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [Valuation.map_neg]
      exact hvly
    · rw [Valuation.map_neg, map_mul]
      calc valuation K (maximalIdeal R) W.toAffine.a₁
            * valuation K (maximalIdeal R)
                (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁)
          ≤ 1 * WithZero.exp (-(s : ℤ)) := mul_le_mul' (valuation_a₁_le_one R W) hv31
        _ = WithZero.exp (-(s : ℤ)) := one_mul _
  have hvy₃ : valuation K (maximalIdeal R)
      (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)) ≤ 1 := by
    rw [← sub_add_cancel (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)) y₁]
    exact Valuation.map_add_le _ (le_trans hvy₃1 (le_of_lt hnegs1)) hy₁

  obtain ⟨h₃', hrS⟩ := reducePoint_some R W (Affine.nonsingular_add h₁ h₂ hxy) hvx₃ hvy₃
  obtain ⟨h₁', hrP⟩ := reducePoint_some R W h₁ hx₁ hy₁
  rw [hrS, hrP]
  obtain ⟨r3x, h3x⟩ := exists_algebraMap_eq_of_valuation_le_one R hvx₃
  obtain ⟨r3y, h3y⟩ := exists_algebraMap_eq_of_valuation_le_one R hvy₃
  simp only [Affine.Point.some.injEq]
  constructor
  · have hsubK : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁
        = algebraMap R K (r3x - r1x) := by
      simp only [map_sub, h3x, h1x]
    have hsub_le : valuation K (maximalIdeal R)
        (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁) ≤ 1 := by
      rw [hsubK]; exact valuation_le_one _ _
    have h0 : reduceCoord R
        (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁) = 0 :=
      (reduceCoord_eq_zero_iff_lt R hsub_le).mpr (lt_of_le_of_lt hv31 hnegs1)
    rw [hsubK, reduceCoord_algebraMap, map_sub, sub_eq_zero] at h0
    rw [← h3x, ← h1x, reduceCoord_algebraMap, reduceCoord_algebraMap]
    exact h0
  · have hsubK : W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) - y₁
        = algebraMap R K (r3y - r1y) := by
      simp only [map_sub, h3y, h1y]
    have hsub_le : valuation K (maximalIdeal R)
        (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) - y₁) ≤ 1 := by
      rw [hsubK]; exact valuation_le_one _ _
    have h0 : reduceCoord R
        (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) - y₁) = 0 :=
      (reduceCoord_eq_zero_iff_lt R hsub_le).mpr (lt_of_le_of_lt hvy₃1 hnegs1)
    rw [hsubK, reduceCoord_algebraMap, map_sub, sub_eq_zero] at h0
    rw [← h3y, ← h1y, reduceCoord_algebraMap, reduceCoord_algebraMap]
    exact h0

end Deep

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    [DecidableEq (IsLocalRing.ResidueField R)]
    (W : WeierstrassCurve K) [W.HasGoodReduction R] {x₁ y₁ x₂ y₂ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx₁ : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x₁ ≤ 1)
    (hx₂ : ¬ IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x₂ ≤ 1) :
    WeierstrassCurve.reducePoint_alt R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = WeierstrassCurve.reducePoint_alt R W (.some x₁ y₁ h₁) :=
  Deep.reducePoint_add_int_pole R W h₁ h₂ hx₁ hx₂

end S_WeierstrassCurve_reducePoint_some_add_some_of_not_le_one
end P2MW
export P2MW.S_WeierstrassCurve_reducePoint_some_add_some_of_not_le_one (solution)
