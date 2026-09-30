-- Prove2me | solution 1 for TranscendenceTheory.bounded_bezout_clear_denominators
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-19T23:42:54.28461+00:00
-- url     : https://prove2.me/submissions/f4d5d629-077b-4048-a47d-05814fa92062

import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.LinearCombination

private theorem clear_one_polynomial
    (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (p : Polynomial K) :
    ∃ d : R, d ≠ 0 ∧ ∃ q : Polynomial R,
      q.map (algebraMap R K) = Polynomial.C (algebraMap R K d) * p ∧
      q.natDegree ≤ p.natDegree := by
  classical
  obtain ⟨d, hd, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  refine ⟨d, nonZeroDivisors.ne_zero hd,
    IsLocalization.integerNormalization (nonZeroDivisors R) p, ?_, ?_⟩
  · rw [hq, Algebra.smul_def, Polynomial.algebraMap_apply]
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    apply Polynomial.notMem_support_iff.mp
    intro hmem
    have hp : n ∉ p.support := Polynomial.notMem_support_iff.mpr
      (Polynomial.coeff_eq_zero_of_natDegree_lt hn)
    exact hp (IsLocalization.integerNormalization_support (nonZeroDivisors R) p hmem)

theorem solution
    (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f g h : Polynomial R) (a b c : ℕ) :
    (∃ u v w : Polynomial K,
      u * f.map (algebraMap R K) + v * g.map (algebraMap R K) +
          w * h.map (algebraMap R K) = 1 ∧
      v.natDegree < b ∧ w.natDegree < c ∧ u.natDegree ≤ a) ↔
    (∃ d : R, d ≠ 0 ∧ ∃ u v w : Polynomial R,
      u * f + v * g + w * h = Polynomial.C d ∧
      v.natDegree < b ∧ w.natDegree < c ∧ u.natDegree ≤ a) := by
  classical
  constructor
  · rintro ⟨u, v, w, hid, hv, hw, hu⟩
    obtain ⟨du, hdu, u₀, hu₀, hdu₀⟩ := clear_one_polynomial R K u
    obtain ⟨dv, hdv, v₀, hv₀, hdv₀⟩ := clear_one_polynomial R K v
    obtain ⟨dw, hdw, w₀, hw₀, hdw₀⟩ := clear_one_polynomial R K w
    refine ⟨du * dv * dw, mul_ne_zero (mul_ne_zero hdu hdv) hdw,
      Polynomial.C (dv * dw) * u₀, Polynomial.C (du * dw) * v₀,
      Polynomial.C (du * dv) * w₀, ?_, ?_, ?_, ?_⟩
    · apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        hu₀, hv₀, hw₀, map_mul, Polynomial.C_mul]
      linear_combination (Polynomial.C (algebraMap R K du) *
        Polynomial.C (algebraMap R K dv) * Polynomial.C (algebraMap R K dw)) * hid
    · exact ((Polynomial.natDegree_C_mul_le _ _).trans hdv₀).trans_lt hv
    · exact ((Polynomial.natDegree_C_mul_le _ _).trans hdw₀).trans_lt hw
    · exact ((Polynomial.natDegree_C_mul_le _ _).trans hdu₀).trans hu
  · rintro ⟨d, hd, u, v, w, hid, hv, hw, hu⟩
    have hdk : algebraMap R K d ≠ 0 := by
      intro hz
      apply hd
      apply IsFractionRing.injective R K
      simpa only [map_zero] using hz
    let e : K := (algebraMap R K d)⁻¹
    have hdegree (p : Polynomial R) :
        (Polynomial.C e * p.map (algebraMap R K)).natDegree ≤ p.natDegree :=
      (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_map_le
    refine ⟨Polynomial.C e * u.map (algebraMap R K),
      Polynomial.C e * v.map (algebraMap R K), Polynomial.C e * w.map (algebraMap R K),
      ?_, (hdegree v).trans_lt hv, (hdegree w).trans_lt hw, (hdegree u).trans hu⟩
    have heq := congrArg (Polynomial.map (algebraMap R K)) hid
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at heq
    calc
      (Polynomial.C e * u.map (algebraMap R K)) * f.map (algebraMap R K) +
          (Polynomial.C e * v.map (algebraMap R K)) * g.map (algebraMap R K) +
          (Polynomial.C e * w.map (algebraMap R K)) * h.map (algebraMap R K) =
          Polynomial.C e * (u.map (algebraMap R K) * f.map (algebraMap R K) +
            v.map (algebraMap R K) * g.map (algebraMap R K) +
            w.map (algebraMap R K) * h.map (algebraMap R K)) := by ring
      _ = Polynomial.C e * Polynomial.C (algebraMap R K d) := by rw [heq]
      _ = 1 := by
        rw [← Polynomial.C_mul, inv_mul_cancel₀ hdk, Polynomial.C_1]
