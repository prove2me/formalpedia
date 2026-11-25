-- Prove2me | solution 1 for UpperTheory.integral_quadratic_half_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:07:47.59349+00:00
-- url     : https://prove2.me/submissions/7a87889a-28d3-4d0d-96a2-474733fdfe4d

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralQuadraticHalfInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private lemma int_of_isIntegral_cast (q : ℚ) (h : IsIntegral ℤ (q : ℂ)) : ∃ n : ℤ, (n : ℚ) = q := by
  have h1 : IsIntegral ℤ (algebraMap ℚ ℂ q) := by simpa using h
  have h2 : IsIntegral ℤ q := (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).1 h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨n, by simpa using hn⟩
private lemma int_of_sq_mul (d : ℕ) (hd : d.Prime) (q : ℚ) (m : ℤ)
    (h : q ^ 2 * (d : ℚ) = m) : ∃ n : ℤ, (n : ℚ) = q := by
  have hq : q * (q.den : ℚ) = q.num := Rat.mul_den_eq_num q
  have h1 : q.num ^ 2 * (d : ℤ) = m * (q.den : ℤ) ^ 2 := by
    have : ((q.num : ℚ)) ^ 2 * (d : ℚ) = (m : ℚ) * (q.den : ℚ) ^ 2 := by
      rw [← hq, ← h]; ring
    exact_mod_cast this
  have hc : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    simpa [Int.gcd] using q.reduced
  have h2 : (q.den : ℤ) ^ 2 ∣ (d : ℤ) :=
    hc.dvd_of_dvd_mul_left ⟨m, by rw [h1]; ring⟩
  have h3 : q.den * q.den ∣ d := by
    have : q.den ^ 2 ∣ d := by exact_mod_cast h2
    rwa [sq] at this
  have h4 : q.den = 1 := Nat.isUnit_iff.1 (hd.prime.squarefree _ h3)
  refine ⟨q.num, ?_⟩
  rw [← hq, h4]; simp
private lemma even_sub_of_norm (d : ℕ) (hd : d.Prime) (x y n : ℤ)
    (h : x ^ 2 + y ^ 2 * (d : ℤ) = 4 * n) : Even (x - y) := by
  obtain ⟨s, hs | hs⟩ := Int.even_or_odd' x <;> obtain ⟨t, ht | ht⟩ := Int.even_or_odd' y
  · exact ⟨s - t, by omega⟩
  · exfalso
    have h1 : (d : ℤ) = 4 * (n - s ^ 2 - (t ^ 2 + t) * d) := by
      rw [hs, ht] at h; linear_combination h
    have h2 : 2 * 2 ∣ d := by
      have : ((4 : ℕ) : ℤ) ∣ (d : ℤ) := ⟨_, by exact_mod_cast h1⟩
      exact_mod_cast this
    have h3 := Nat.isUnit_iff.1 (hd.prime.squarefree _ h2)
    omega
  · exfalso
    have h1 : (1 : ℤ) = 4 * (n - s ^ 2 - s - t ^ 2 * d) := by
      rw [hs, ht] at h; linear_combination h
    omega
  · exact ⟨s - t, by omega⟩
end

set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ (d : ℕ), d.Prime → ∀ (a b : ℚ), IsIntegral ℤ ((a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))) → ∃ x y : ℤ, Even (x - y) ∧ (a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) = ((x : ℂ) + (y : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))) / 2 := by
  intro d hd a b h
  have hr : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    have : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
    exact_mod_cast this
  generalize Real.sqrt (d : ℝ) = r at h hr ⊢
  have h' : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ))) := by
    have h0 := map_isIntegral_int (starRingEnd ℂ) h
    have e : (starRingEnd ℂ) ((a : ℂ) + (b : ℂ) * (Complex.I * (r : ℂ)))
        = (a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ)) := by
      simp only [map_add, map_mul, map_ratCast, Complex.conj_I, Complex.conj_ofReal]
      ring
    rwa [e] at h0
  obtain ⟨x, hx⟩ := int_of_isIntegral_cast (2 * a) (by
    have e : ((2 * a : ℚ) : ℂ) = ((a : ℂ) + (b : ℂ) * (Complex.I * (r : ℂ)))
        + ((a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ))) := by
      push_cast; ring
    rw [e]; exact h.add h')
  obtain ⟨n, hn⟩ := int_of_isIntegral_cast (a ^ 2 + b ^ 2 * d) (by
    have e : ((a ^ 2 + b ^ 2 * d : ℚ) : ℂ) = ((a : ℂ) + (b : ℂ) * (Complex.I * (r : ℂ)))
        * ((a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ))) := by
      push_cast
      linear_combination (b : ℂ) ^ 2 * (r : ℂ) ^ 2 * Complex.I_sq - (b : ℂ) ^ 2 * hr
    rw [e]; exact h.mul h')
  obtain ⟨y, hy⟩ := int_of_sq_mul d hd (2 * b) (4 * n - x ^ 2) (by
    push_cast
    rw [hn, hx]; ring)
  refine ⟨x, y, even_sub_of_norm d hd x y n ?_, ?_⟩
  · have : (x : ℚ) ^ 2 + (y : ℚ) ^ 2 * (d : ℚ) = 4 * n := by
      rw [hx, hy, hn]; ring
    exact_mod_cast this
  · have hx' : (x : ℂ) = 2 * (a : ℂ) := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) hx
    have hy' : (y : ℂ) = 2 * (b : ℂ) := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) hy
    rw [hx', hy']; ring
end UpperTheory
