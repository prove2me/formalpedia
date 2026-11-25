-- Prove2me | solution 1 for UpperTheory.integral_imag_quadratic_half_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:07:46.055848+00:00
-- url     : https://prove2.me/submissions/41c2f902-13f3-4dda-bdc0-2af7713fad29

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralImagQuadraticHalfInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
private lemma coords {E : Type} [Field E] [CharZero E] (d : ℕ) (s : E) (hs : s ^ 2 = -(d : E))
    (z : E) (hz : z ∈ IntermediateField.adjoin ℚ ({s} : Set E)) :
    ∃ a b : ℚ, z = (a : E) + (b : E) * s := by
  have hint : IsIntegral ℚ s := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hs]
    exact (isIntegral_natCast d).neg
  have hz' : z ∈ Algebra.adjoin ℚ ({s} : Set E) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hz
  clear hz
  induction hz' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    push_cast
    linear_combination (b : E) * e * hs
private lemma aeval_pair {E : Type} [Field E] [CharZero E] (d : ℕ) (s : E) (hs : s ^ 2 = -(d : E))
    (a b : ℚ) (p : ℤ[X]) :
    ∃ u v : ℚ, aeval ((a : E) + (b : E) * s) p = (u : E) + (v : E) * s ∧
      aeval ((a : E) - (b : E) * s) p = (u : E) - (v : E) * s := by
  induction p using Polynomial.induction_on with
  | C c => exact ⟨c, 0, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨u, v, h1, h2⟩ := hp
    obtain ⟨u', v', h1', h2'⟩ := hq
    refine ⟨u + u', v + v', ?_, ?_⟩
    · rw [map_add, h1, h1']; push_cast; ring
    · rw [map_add, h2, h2']; push_cast; ring
  | monomial n c h =>
    obtain ⟨u, v, h1, h2⟩ := h
    refine ⟨u * a - d * v * b, u * b + v * a, ?_, ?_⟩
    · rw [pow_succ, ← mul_assoc, map_mul, h1, aeval_X]
      push_cast
      linear_combination (v : E) * b * hs
    · rw [pow_succ, ← mul_assoc, map_mul, h2, aeval_X]
      push_cast
      linear_combination (v : E) * b * hs
private lemma conj_integral {E : Type} [Field E] [CharZero E] (d : ℕ) (s : E) (hd : 0 < d)
    (hs : s ^ 2 = -(d : E)) (a b : ℚ) (h : IsIntegral ℤ ((a : E) + (b : E) * s)) :
    IsIntegral ℤ ((a : E) - (b : E) * s) := by
  obtain ⟨p, hp, h0⟩ := h
  obtain ⟨u, v, h1, h2⟩ := aeval_pair d s hs a b p
  rw [← aeval_def, h1] at h0
  have hn : u ^ 2 + d * v ^ 2 = 0 := by
    have : (u : E) ^ 2 + d * (v : E) ^ 2 = 0 := by
      linear_combination ((u : E) - v * s) * h0 + (v : E) ^ 2 * hs
    exact_mod_cast this
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hv2 : 0 ≤ (d : ℚ) * v ^ 2 := by positivity
  have hu : u = 0 := by nlinarith [sq_nonneg u]
  have hv : v = 0 := by
    rw [hu] at hn
    have : (d : ℚ) * v ^ 2 = 0 := by simpa using hn
    simpa [hd'.ne'] using this
  refine ⟨p, hp, ?_⟩
  rw [← aeval_def, h2, hu, hv]
  simp
private lemma rat_int {E : Type} [Field E] [CharZero E] (q : ℚ) (h : IsIntegral ℤ (q : E)) :
    ∃ n : ℤ, (n : ℚ) = q := by
  have h' : IsIntegral ℤ q := by
    have := (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := E) (x := q)
      (algebraMap ℚ E).injective).1 (by simpa using h)
    exact this
  simpa using (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 h'
private lemma int_of_sqfree_mul_sq (d : ℕ) (hd : Squarefree d) (q : ℚ) (m : ℤ)
    (h : (m : ℚ) = d * q ^ 2) : ∃ n : ℤ, (n : ℚ) = q := by
  have h1 : q * q.den = q.num := Rat.mul_den_eq_num q
  have h2 : (d : ℤ) * q.num ^ 2 = (q.den : ℤ) ^ 2 * m := by
    have : (d : ℚ) * (q.num : ℚ) ^ 2 = (q.den : ℚ) ^ 2 * m := by
      rw [← h1, h]; ring
    exact_mod_cast this
  have hc : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) :=
    (Rat.isCoprime_num_den q).symm.pow
  have h3 : (q.den : ℤ) ^ 2 ∣ d := hc.dvd_of_dvd_mul_right ⟨m, h2⟩
  have h4 : q.den * q.den ∣ d := by
    rw [← sq]; exact_mod_cast h3
  have h5 : q.den = 1 := Nat.isUnit_iff.1 (hd _ h4)
  exact ⟨q.num, by rw [← h1, h5]; simp⟩
end

set_option autoImplicit false
open Polynomial
namespace UpperTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [CharZero E] (d : ℕ) (s : E), Squarefree d → s ^ 2 = -(d : E) → ∀ z : E, z ∈ IntermediateField.adjoin ℚ ({s} : Set E) → IsIntegral ℤ z → ∃ x y : ℤ, Even (x - y) ∧ z = ((x : E) + (y : E) * s) / 2 := by
  intro E _ _ d s hd hs z hz hi
  obtain ⟨a, b, rfl⟩ := coords d s hs z hz
  have hc := conj_integral d s (Nat.pos_of_ne_zero hd.ne_zero) hs a b hi
  obtain ⟨x, hx⟩ := rat_int (E := E) (2 * a) (by
    have e : ((2 * a : ℚ) : E) = (a : E) + (b : E) * s + ((a : E) - (b : E) * s) := by
      push_cast; ring
    rw [e]
    exact hi.add hc)
  obtain ⟨n, hn⟩ := rat_int (E := E) (a ^ 2 + d * b ^ 2) (by
    have e : ((a ^ 2 + d * b ^ 2 : ℚ) : E)
        = ((a : E) + (b : E) * s) * ((a : E) - (b : E) * s) := by
      push_cast
      linear_combination (b : E) ^ 2 * hs
    rw [e]
    exact hi.mul hc)
  obtain ⟨y, hy⟩ := int_of_sqfree_mul_sq d hd (2 * b) (4 * n - x ^ 2) (by
    push_cast
    rw [hx, hn]; ring)
  have key : x ^ 2 + d * y ^ 2 = 4 * n := by
    have : (x : ℚ) ^ 2 + d * (y : ℚ) ^ 2 = 4 * n := by
      rw [hx, hy, hn]; ring
    exact_mod_cast this
  refine ⟨x, y, ?_, ?_⟩
  · rcases Int.even_or_odd' x with ⟨k, rfl | rfl⟩ <;>
      rcases Int.even_or_odd' y with ⟨l, rfl | rfl⟩
    · exact ⟨k - l, by ring⟩
    · exfalso
      have h4 : (4 : ℤ) ∣ d := ⟨n - k ^ 2 - d * (l ^ 2 + l), by linear_combination key⟩
      have h5 : 2 * 2 ∣ d := by exact_mod_cast h4
      simpa using hd 2 h5
    · exfalso
      have h4 : 4 * (n - k ^ 2 - k - d * l ^ 2) = 1 := by linear_combination -key
      omega
    · exact ⟨k - l, by ring⟩
  · have hx' : (x : E) = 2 * (a : E) := by exact_mod_cast congrArg (fun t : ℚ => (t : E)) hx
    have hy' : (y : E) = 2 * (b : E) := by exact_mod_cast congrArg (fun t : ℚ => (t : E)) hy
    rw [hx', hy']; ring
end UpperTheory
