-- Prove2me | solution 1 for SelbergOptimization.supported_weights
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T22:32:41.926704+00:00
-- url     : https://prove2.me/submissions/3551d487-fe69-4cdd-8970-e620c5f031a6

import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic

set_option autoImplicit false
open scoped BigOperators

namespace SelbergOptimization

/-!
Upper-divisor Möbius inversion on the divisors of one positive integer.
This is a standalone draft against Lean 4.33.1 / Mathlib 0df444a.
No sieve conclusion, squarefreeness, or support property is assumed.
The proof conjugates ordinary divisor inversion by the complement map d ↦ P/d.
-/

/-- The upper incidence-algebra inverse used to construct the Selberg weights. -/
noncomputable def upperMoebiusInverse (P : ℕ) (Y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ e ∈ P.divisors,
    if d ∣ e then (ArithmeticFunction.moebius (e / d) : ℝ) * Y e else 0

/-- Multiples of d among the divisors of P are d times the divisors of P/d. -/
theorem sum_over_upper_divisors (P d : ℕ) (hP : P ≠ 0) (hd : d ∣ P)
    (f : ℕ → ℝ) :
    (∑ e ∈ P.divisors, if d ∣ e then f e else 0) =
      ∑ a ∈ (P / d).divisors, f (d * a) := by
  classical
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hP hd
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hn0 : P / d ≠ 0 := by
    intro h
    have heq := Nat.mul_div_cancel' hd
    rw [h, Nat.mul_zero] at heq
    exact hP heq.symm
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun a _ => d * a)
  · intro a ha
    have haP : d * a ∣ P := by
      have h := Nat.mul_dvd_mul_left d (Nat.dvd_of_mem_divisors ha)
      simpa only [Nat.mul_div_cancel' hd] using h
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨haP, hP⟩, Nat.dvd_mul_right d a⟩
  · intro a₁ ha₁ a₂ ha₂ heq
    exact Nat.eq_of_mul_eq_mul_left hdpos heq
  · intro e he
    obtain ⟨heP, hde⟩ := Finset.mem_filter.mp he
    refine ⟨e / d, Nat.mem_divisors.mpr
      ⟨Nat.div_dvd_div hde (Nat.dvd_of_mem_divisors heP), hn0⟩, ?_⟩
    exact Nat.mul_div_cancel' hde
  · intro a ha
    rfl

/-- Complementation converts an upper-divisor sum into an ordinary divisor sum. -/
theorem sum_upper_complement (P l : ℕ) (hP : P ≠ 0) (hl : l ∣ P)
    (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then f (P / d) else 0) =
      ∑ a ∈ (P / l).divisors, f a := by
  rw [sum_over_upper_divisors P l hP hl]
  simp_rw [← Nat.div_div_eq_div_mul]
  exact Nat.sum_div_divisors (P / l) f

/-- Ordinary Möbius inversion applied to the complemented source. -/
noncomputable def lowerComplementInverse (P : ℕ) (Y : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ n.divisorsAntidiagonal,
    (ArithmeticFunction.moebius x.1 : ℝ) * Y (P / x.2)

theorem lower_complement_sum (P : ℕ) (Y : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    (∑ a ∈ n.divisors, lowerComplementInverse P Y a) = Y (P / n) := by
  have h :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := lowerComplementInverse P Y) (g := fun r => Y (P / r))).mpr
      (by intro r hr; rfl)
  exact h n hn

/-- The two explicit formulas agree on each actual divisor of P. -/
theorem upper_inverse_eq_lower_complement (P : ℕ) (hP : P ≠ 0)
    (Y : ℕ → ℝ) (d : ℕ) (hd : d ∣ P) :
    upperMoebiusInverse P Y d = lowerComplementInverse P Y (P / d) := by
  classical
  have hdpos : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hd)
  have hn0 : P / d ≠ 0 := by
    intro h
    have heq := Nat.mul_div_cancel' hd
    rw [h, Nat.mul_zero] at heq
    exact hP heq.symm
  unfold upperMoebiusInverse
  rw [sum_over_upper_divisors P d hP hd]
  unfold lowerComplementInverse
  rw [Nat.sum_divisorsAntidiagonal
    (fun a b : ℕ => (ArithmeticFunction.moebius a : ℝ) * Y (P / b))]
  apply Finset.sum_congr rfl
  intro a ha
  have hadvd : a ∣ P / d := Nat.dvd_of_mem_divisors ha
  have hquot : P / ((P / d) / a) = d * a := by
    calc
      _ = (d * (P / d)) / ((P / d) / a) := by rw [Nat.mul_div_cancel' hd]
      _ = d * ((P / d) / ((P / d) / a)) :=
        Nat.mul_div_assoc d (Nat.div_dvd_of_dvd hadvd)
      _ = d * a := by rw [Nat.div_div_self hadvd hn0]
  rw [Nat.mul_div_cancel_left _ hdpos, hquot]

/-- Upper-divisor Möbius inversion, with no condition on the function Y. -/
theorem upper_sum_inverse (P : ℕ) (hP : P ≠ 0) (Y : ℕ → ℝ)
    (l : ℕ) (hl : l ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d then upperMoebiusInverse P Y d else 0) = Y l := by
  classical
  have hn0 : P / l ≠ 0 := by
    intro h
    have heq := Nat.mul_div_cancel' hl
    rw [h, Nat.mul_zero] at heq
    exact hP heq.symm
  calc
    _ = ∑ d ∈ P.divisors,
        if l ∣ d then lowerComplementInverse P Y (P / d) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hld : l ∣ d
      · rw [if_pos hld, if_pos hld,
          upper_inverse_eq_lower_complement P hP Y d (Nat.dvd_of_mem_divisors hd)]
      · rw [if_neg hld, if_neg hld]
    _ = ∑ a ∈ (P / l).divisors, lowerComplementInverse P Y a :=
      sum_upper_complement P l hP hl (lowerComplementInverse P Y)
    _ = Y (P / (P / l)) :=
      lower_complement_sum P Y (P / l) (Nat.pos_of_ne_zero hn0)
    _ = Y l := by rw [Nat.div_div_self hl hP]

end SelbergOptimization


namespace SelbergOptimization
open scoped ArithmeticFunction.Moebius
open Finset Nat BoundingSieve

noncomputable def denominator (s : BoundingSieve) (z : ℝ) : ℝ :=
  ∑ e ∈ s.prodPrimes.divisors, if (e : ℝ) ≤ z then s.selbergTerms e else 0

noncomputable def diagonalTarget (s : BoundingSieve) (z : ℝ) (e : ℕ) : ℝ :=
  if (e : ℝ) ≤ z then (μ e : ℝ) * s.selbergTerms e / denominator s z else 0

noncomputable def sieveWeight (s : BoundingSieve) (z : ℝ) (d : ℕ) : ℝ :=
  upperMoebiusInverse s.prodPrimes (diagonalTarget s z) d / s.nu d

theorem denominator_pos (s : BoundingSieve) (z : ℝ) (hz : 1 ≤ z) :
    0 < denominator s z := by
  have hone : 1 ∈ s.prodPrimes.divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, s.prodPrimes_ne_zero⟩
  have hnonneg (e : ℕ) (he : e ∈ s.prodPrimes.divisors) :
      0 ≤ if (e : ℝ) ≤ z then s.selbergTerms e else 0 := by
    split_ifs
    · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors he)).le
    · exact le_rfl
  have hle := Finset.single_le_sum hnonneg hone
  have hg1 : s.selbergTerms 1 = 1 := s.selbergTerms_isMultiplicative.map_one
  have : 1 ≤ denominator s z := by simpa [denominator, hz, hg1] using hle
  linarith

private theorem real_moebius_sq (s : BoundingSieve) {d : ℕ}
    (hd : d ∈ s.prodPrimes.divisors) : (μ d : ℝ) ^ 2 = 1 := by
  exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
    (s.squarefree_of_mem_divisors_prodPrimes hd)

theorem sieveWeight_one (s : BoundingSieve) (z : ℝ) (hz : 1 ≤ z) :
    sieveWeight s z 1 = 1 := by
  have hD := (denominator_pos s z hz).ne'
  have hnu : s.nu 1 = 1 := s.nu_mult.map_one
  rw [sieveWeight, hnu, div_one, upperMoebiusInverse]
  simp only [one_dvd, if_true, Nat.div_one]
  calc
    (∑ e ∈ s.prodPrimes.divisors, (μ e : ℝ) * diagonalTarget s z e) =
        ∑ e ∈ s.prodPrimes.divisors,
          (if (e : ℝ) ≤ z then s.selbergTerms e else 0) / denominator s z := by
      apply Finset.sum_congr rfl
      intro e he
      unfold diagonalTarget
      split_ifs with h
      · have hm := real_moebius_sq s he
        calc
          _ = (μ e : ℝ)^2 * s.selbergTerms e / denominator s z := by ring
          _ = _ := by rw [hm, one_mul]
      · simp
    _ = denominator s z / denominator s z := by simp only [div_eq_mul_inv, ← Finset.sum_mul]; rfl
    _ = 1 := div_self hD

theorem sieveWeight_above_level (s : BoundingSieve) (z : ℝ) (d : ℕ)
    (hdz : z < (d : ℝ)) : sieveWeight s z d = 0 := by
  unfold sieveWeight upperMoebiusInverse
  suffices (∑ e ∈ s.prodPrimes.divisors,
      if d ∣ e then (μ (e / d) : ℝ) * diagonalTarget s z e else 0) = 0 by
    rw [this, zero_div]
  apply Finset.sum_eq_zero
  intro e he
  by_cases hde : d ∣ e
  · have he0 : 0 < e := Nat.pos_of_ne_zero
      (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero (Nat.dvd_of_mem_divisors he))
    have hle : (d : ℝ) ≤ e := by exact_mod_cast Nat.le_of_dvd he0 hde
    have hnot : ¬ (e : ℝ) ≤ z := by linarith
    simp [hde, diagonalTarget, hnot]
  · simp [hde]

theorem sieveWeight_diagonal (s : BoundingSieve) (z : ℝ) (l : ℕ)
    (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
      if l ∣ d then s.nu d * sieveWeight s z d else 0) = diagonalTarget s z l := by
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors,
      if l ∣ d then upperMoebiusInverse s.prodPrimes (diagonalTarget s z) d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hnu := s.nu_ne_zero (Nat.dvd_of_mem_divisors hd)
      simp only [sieveWeight]
      split_ifs
      · exact mul_div_cancel₀ _ hnu
      · rfl
    _ = _ := upper_sum_inverse s.prodPrimes s.prodPrimes_ne_zero (diagonalTarget s z) l hl

theorem sieveWeight_mainSum (s : BoundingSieve) (z : ℝ) (hz : 1 ≤ z) :
    s.mainSum (lambdaSquared (sieveWeight s z)) = (denominator s z)⁻¹ := by
  have hD := (denominator_pos s z hz).ne'
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  calc
    (∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
      (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * sieveWeight s z d else 0)^2) =
        ∑ l ∈ s.prodPrimes.divisors,
          (if (l : ℝ) ≤ z then s.selbergTerms l else 0) / (denominator s z)^2 := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [sieveWeight_diagonal s z l (Nat.dvd_of_mem_divisors hl)]
      unfold diagonalTarget
      split_ifs with h
      · have hg := (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)).ne'
        have hm := real_moebius_sq s hl
        rw [div_pow, mul_pow, hm, one_mul]
        field_simp
      · simp
    _ = denominator s z / (denominator s z)^2 := by simp only [div_eq_mul_inv, ← Finset.sum_mul]; rfl
    _ = (denominator s z)⁻¹ := by field_simp

/-- Explicit supported Selberg weights give the reciprocal-denominator main term.
The error remains the actual library remainder sum; no error estimate is assumed. -/
theorem siftedSum_le_denominator_inv (s : BoundingSieve) (z : ℝ) (hz : 1 ≤ z) :
    s.siftedSum ≤ s.totalMass / denominator s z +
      s.errSum (lambdaSquared (sieveWeight s z)) := by
  have h := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (lambdaSquared (sieveWeight s z))
    (upperMoebius_lambdaSquared _ (sieveWeight_one s z hz))
  simpa only [sieveWeight_mainSum s z hz, div_eq_mul_inv] using h

end SelbergOptimization


theorem solution (s : BoundingSieve) (z : ℝ) (hz : 1 ≤ z) :
    ∃ w : ℕ → ℝ, w 1 = 1 ∧ (∀ d : ℕ, z < (d : ℝ) → w d = 0) ∧
      s.mainSum (BoundingSieve.lambdaSquared w) =
        (∑ e ∈ s.prodPrimes.divisors, if (e : ℝ) ≤ z then s.selbergTerms e else 0)⁻¹ ∧
      s.siftedSum ≤ s.totalMass /
        (∑ e ∈ s.prodPrimes.divisors, if (e : ℝ) ≤ z then s.selbergTerms e else 0) +
        s.errSum (BoundingSieve.lambdaSquared w) := by
  exact ⟨SelbergOptimization.sieveWeight s z,
    SelbergOptimization.sieveWeight_one s z hz,
    SelbergOptimization.sieveWeight_above_level s z,
    SelbergOptimization.sieveWeight_mainSum s z hz,
    SelbergOptimization.siftedSum_le_denominator_inv s z hz⟩

#print axioms solution
