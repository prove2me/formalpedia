-- Prove2me | solution 1 for WeierstrassCurve.exists_valuation_eq_exp_of_not_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fc8aa135-b487-5b6f-847e-2fac4924c711

import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_valuation_eq_exp_of_not_le_one

set_option autoImplicit false

open WeierstrassCurve IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace PoleDichotomy

theorem valuation_dichotomy (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K) [W.IsIntegral R] {x y : K} (h : W.toAffine.Equation x y)
    (hx : ¬ valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1) :
    ∃ s : ℕ, 0 < s ∧
      valuation K (IsDiscreteValuationRing.maximalIdeal R) x
        = WithZero.exp (2 * (s : ℤ)) ∧
      valuation K (IsDiscreteValuationRing.maximalIdeal R) y
        = WithZero.exp (3 * (s : ℤ)) := by
  set v := valuation K (IsDiscreteValuationRing.maximalIdeal R) with hv

  have key : ∀ z : K, (∃ r : R, algebraMap R K r = z) → v z ≤ 1 := by
    rintro z ⟨r, rfl⟩; exact valuation_le_one (IsDiscreteValuationRing.maximalIdeal R) r
  have ha1 : v W.toAffine.a₁ ≤ 1 := key _ ⟨_, integralModel_a₁_eq R W⟩
  have ha2 : v W.toAffine.a₂ ≤ 1 := key _ ⟨_, integralModel_a₂_eq R W⟩
  have ha3 : v W.toAffine.a₃ ≤ 1 := key _ ⟨_, integralModel_a₃_eq R W⟩
  have ha4 : v W.toAffine.a₄ ≤ 1 := key _ ⟨_, integralModel_a₄_eq R W⟩
  have ha6 : v W.toAffine.a₆ ≤ 1 := key _ ⟨_, integralModel_a₆_eq R W⟩

  have hpow : ∀ (n : ℕ) (c : ℤ), WithZero.exp c ^ n = WithZero.exp ((n : ℤ) * c) := by
    intro n c
    rw [← WithZero.exp_nsmul, nsmul_eq_mul]

  have hvx1 : 1 < v x := not_le.mp hx
  have hvx0 : v x ≠ 0 := (zero_lt_one.trans hvx1).ne'
  obtain ⟨a, hax⟩ : ∃ a : ℤ, v x = WithZero.exp a := ⟨_, (WithZero.exp_log hvx0).symm⟩
  have ha0 : 0 < a := by
    have h1 : WithZero.exp (0 : ℤ) < WithZero.exp a := by
      rw [WithZero.exp_zero, ← hax]; exact hvx1
    exact WithZero.exp_lt_exp.mp h1

  have hx3 : v (x ^ 3) = WithZero.exp (3 * a) := by
    rw [map_pow, hax, hpow]; norm_num
  have hA2 : v (W.toAffine.a₂ * x ^ 2) ≤ WithZero.exp (2 * a) := by
    calc v (W.toAffine.a₂ * x ^ 2) = v W.toAffine.a₂ * WithZero.exp (2 * a) := by
          rw [map_mul, map_pow, hax, hpow]; norm_num
      _ ≤ 1 * WithZero.exp (2 * a) := mul_le_mul' ha2 le_rfl
      _ = WithZero.exp (2 * a) := one_mul _
  have hA4 : v (W.toAffine.a₄ * x) ≤ WithZero.exp a := by
    calc v (W.toAffine.a₄ * x) = v W.toAffine.a₄ * WithZero.exp a := by rw [map_mul, hax]
      _ ≤ 1 * WithZero.exp a := mul_le_mul' ha4 le_rfl
      _ = WithZero.exp a := one_mul _
  have h1 : v (x ^ 3 + W.toAffine.a₂ * x ^ 2) = WithZero.exp (3 * a) := by
    rw [← hx3]
    exact v.map_add_eq_of_lt_left
      (hx3 ▸ lt_of_le_of_lt hA2 (WithZero.exp_lt_exp.mpr (by omega)))
  have h2 : v (x ^ 3 + W.toAffine.a₂ * x ^ 2 + W.toAffine.a₄ * x) = WithZero.exp (3 * a) := by
    rw [← h1]
    exact v.map_add_eq_of_lt_left
      (h1 ▸ lt_of_le_of_lt hA4 (WithZero.exp_lt_exp.mpr (by omega)))
  have hRHS : v (x ^ 3 + W.toAffine.a₂ * x ^ 2 + W.toAffine.a₄ * x + W.toAffine.a₆)
      = WithZero.exp (3 * a) := by
    rw [← h2]
    refine v.map_add_eq_of_lt_left (h2 ▸ lt_of_le_of_lt ha6 ?_)
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)

  rw [Affine.equation_iff] at h
  have hLHS : v (y ^ 2 + W.toAffine.a₁ * x * y + W.toAffine.a₃ * y) = WithZero.exp (3 * a) := by
    rw [h]; exact hRHS

  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, mul_zero, mul_zero, add_zero, add_zero, map_zero] at hLHS
    exact WithZero.exp_ne_zero hLHS.symm
  have hvy0 : v y ≠ 0 := fun h0 => hy0 (v.zero_iff.mp h0)
  obtain ⟨b, hby⟩ : ∃ b : ℤ, v y = WithZero.exp b := ⟨_, (WithZero.exp_log hvy0).symm⟩
  have hy2 : v (y ^ 2) = WithZero.exp (2 * b) := by
    rw [map_pow, hby, hpow]; norm_num
  have hA1 : v (W.toAffine.a₁ * x * y) ≤ WithZero.exp (a + b) := by
    calc v (W.toAffine.a₁ * x * y)
        = v W.toAffine.a₁ * (WithZero.exp a * WithZero.exp b) := by
          rw [map_mul, map_mul, mul_assoc, hax, hby]
      _ ≤ 1 * (WithZero.exp a * WithZero.exp b) := mul_le_mul' ha1 le_rfl
      _ = WithZero.exp (a + b) := by rw [one_mul, ← WithZero.exp_add]
  have hA3 : v (W.toAffine.a₃ * y) ≤ WithZero.exp b := by
    calc v (W.toAffine.a₃ * y) = v W.toAffine.a₃ * WithZero.exp b := by rw [map_mul, hby]
      _ ≤ 1 * WithZero.exp b := mul_le_mul' ha3 le_rfl
      _ = WithZero.exp b := one_mul _

  rcases lt_trichotomy (2 * b) (3 * a) with hlt | heq2 | hgt
  ·
    exfalso
    have ht1 : v (y ^ 2) < WithZero.exp (3 * a) := by
      rw [hy2]; exact WithZero.exp_lt_exp.mpr hlt
    have ht2 : v (W.toAffine.a₁ * x * y) < WithZero.exp (3 * a) :=
      lt_of_le_of_lt hA1 (WithZero.exp_lt_exp.mpr (by omega))
    have ht3 : v (W.toAffine.a₃ * y) < WithZero.exp (3 * a) :=
      lt_of_le_of_lt hA3 (WithZero.exp_lt_exp.mpr (by omega))
    exact (v.map_add_lt (v.map_add_lt ht1 ht2) ht3).ne hLHS
  ·
    refine ⟨(b - a).toNat, by omega, ?_, ?_⟩
    · rw [hax]; congr 1; omega
    · rw [hby]; congr 1; omega
  ·
    exfalso
    have ht2 : v (W.toAffine.a₁ * x * y) < v (y ^ 2) := by
      rw [hy2]; exact lt_of_le_of_lt hA1 (WithZero.exp_lt_exp.mpr (by omega))
    have ht3 : v (W.toAffine.a₃ * y) < v (y ^ 2) := by
      rw [hy2]; exact lt_of_le_of_lt hA3 (WithZero.exp_lt_exp.mpr (by omega))
    rw [add_assoc] at hLHS
    have hdom : v (y ^ 2 + (W.toAffine.a₁ * x * y + W.toAffine.a₃ * y)) = v (y ^ 2) :=
      v.map_add_eq_of_lt_left (v.map_add_lt ht2 ht3)
    rw [hdom, hy2] at hLHS
    exact absurd (WithZero.exp_inj.mp hLHS) (by omega)

end PoleDichotomy

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.IsIntegral R] {x y : K} (h : W.toAffine.Equation x y)
    (hx : ¬ IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1) :
    ∃ s : ℕ, 0 < s ∧
      IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x = WithZero.exp (2 * (s : ℤ)) ∧
      IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) y = WithZero.exp (3 * (s : ℤ)) :=
  PoleDichotomy.valuation_dichotomy R W h hx

end S_WeierstrassCurve_exists_valuation_eq_exp_of_not_le_one
end P2MW
export P2MW.S_WeierstrassCurve_exists_valuation_eq_exp_of_not_le_one (solution)
