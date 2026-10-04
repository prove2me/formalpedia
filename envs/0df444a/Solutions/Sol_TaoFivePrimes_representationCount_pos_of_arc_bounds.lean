-- Prove2me | solution 1 for TaoFivePrimes.representationCount_pos_of_arc_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-07T04:04:29.421896+00:00
-- url     : https://prove2.me/submissions/2d658337-6eb1-4238-b309-d16166e81cdc

import Definitions.Def_TaoFivePrimes_FourierRepresentation
import Mathlib.Tactic.Linarith


open MeasureTheory
open scoped BigOperators

namespace TaoFourierIdentity

theorem continuous_fourierPolynomial {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (k : ι → ℤ) : Continuous (fourierPolynomial s a k) := by
  unfold fourierPolynomial
  exact continuous_finsetSum s (fun i _ ↦ continuous_const.mul (fourier (k i)).continuous)

theorem integral_fourier (k : ℤ) :
    (∫ α : AddCircle (1 : ℝ), fourier k α ∂AddCircle.haarAddCircle) =
      if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

theorem integral_fourier_term (a : ℂ) (k m : ℤ) :
    (∫ α : AddCircle (1 : ℝ), a * fourier k α * fourier (-m) α
      ∂AddCircle.haarAddCircle) = if k = m then a else 0 := by
  simp_rw [mul_assoc, ← fourier_add]
  rw [integral_const_mul, integral_fourier]
  by_cases h : k = m
  · simp [h]
  · have hn : k + -m ≠ 0 := by omega
    simp [h, hn]

theorem integral_fourierPolynomial {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (k : ι → ℤ) (m : ℤ) :
    (∫ α : AddCircle (1 : ℝ), fourierPolynomial s a k α * fourier (-m) α
      ∂AddCircle.haarAddCircle) = ∑ i ∈ s, if k i = m then a i else 0 := by
  unfold fourierPolynomial
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ ↦ integral_fourier_term (a i) (k i) m)
  · intro i _
    exact ((continuous_const.mul (fourier (k i)).continuous).mul
      (fourier (-m)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem fourierPolynomial_mul {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (k : ι → ℤ) (l : κ → ℤ)
    (α : AddCircle (1 : ℝ)) :
    fourierPolynomial s a k α * fourierPolynomial t b l α =
      fourierPolynomial (s ×ˢ t) (fun p ↦ a p.1 * b p.2)
        (fun p ↦ k p.1 + l p.2) α := by
  simp only [fourierPolynomial, Finset.sum_product, Finset.sum_mul, Finset.mul_sum,
    fourier_add]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  exact Finset.sum_comm

end TaoFourierIdentity

namespace TaoFourierIdentity

theorem sixfold_fourier_count (s t u : Finset ℕ) (a b : ℕ → ℂ) (x : ℕ) :
    (∫ α : AddCircle (1 : ℝ),
      fourierPolynomial s a (fun n ↦ (n : ℤ)) α ^ 2 *
      fourierPolynomial t b (fun n ↦ (n : ℤ)) α *
      fourierPolynomial u (fun _ ↦ 1) (fun n ↦ (n : ℤ)) α ^ 3 *
      fourier (-(x : ℤ)) α ∂AddCircle.haarAddCircle) =
    ∑ n₁ ∈ s, ∑ n₂ ∈ s, ∑ n₃ ∈ t,
      ∑ h₁ ∈ u, ∑ h₂ ∈ u, ∑ h₃ ∈ u,
        if x = n₁ + n₂ + n₃ + h₁ + h₂ + h₃ then a n₁ * a n₂ * b n₃ else 0 := by
  classical
  have hexpand (A B D : ℂ) : A ^ 2 * B * D ^ 3 = (((((A * A) * B) * D) * D) * D) := by
    ring
  simp_rw [hexpand, fourierPolynomial_mul]
  rw [integral_fourierPolynomial]
  have hcast (n₁ n₂ n₃ h₁ h₂ h₃ : ℕ) :
      ((n₁ : ℤ) + n₂ + n₃ + h₁ + h₂ + h₃ = (x : ℤ)) ↔
        x = n₁ + n₂ + n₃ + h₁ + h₂ + h₃ := by omega
  simp only [Finset.sum_product, mul_one, hcast]

theorem representationCount_eq_fourier_integral (x H : ℕ) :
    (TaoFivePrimes.representationCount x H : ℂ) =
    ∫ α : AddCircle (1 : ℝ),
      fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (TaoFivePrimes.siftedVonMangoldt x n *
          TaoFivePrimes.eta1 ((n : ℝ) / x) : ℝ)) (fun n ↦ (n : ℤ)) α ^ 2 *
      fourierPolynomial (Finset.range (x / 1000 + 1))
        (fun n ↦ (TaoFivePrimes.siftedVonMangoldt (x / 1000) n *
          TaoFivePrimes.eta0 (1000 * (n : ℝ) / x) : ℝ)) (fun n ↦ (n : ℤ)) α *
      fourierPolynomial (Finset.Icc 1 (H / 3)) (fun _ ↦ 1) (fun n ↦ (n : ℤ)) α ^ 3 *
      fourier (-(x : ℤ)) α ∂AddCircle.haarAddCircle := by
  rw [sixfold_fourier_count]
  simp [TaoFivePrimes.representationCount, apply_ite, mul_assoc]

end TaoFourierIdentity

namespace TaoFourierIdentity

theorem integrable_sixfold_fourier_count (s t u : Finset ℕ) (a b : ℕ → ℂ) (x : ℕ) :
    Integrable (fun α : AddCircle (1 : ℝ) ↦
      fourierPolynomial s a (fun n ↦ (n : ℤ)) α ^ 2 *
      fourierPolynomial t b (fun n ↦ (n : ℤ)) α *
      fourierPolynomial u (fun _ ↦ 1) (fun n ↦ (n : ℤ)) α ^ 3 *
      fourier (-(x : ℤ)) α) AddCircle.haarAddCircle := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact (((continuous_fourierPolynomial s a _).pow 2).mul
    (continuous_fourierPolynomial t b _)).mul
      ((continuous_fourierPolynomial u (fun _ ↦ 1) _).pow 3) |>.mul
        (fourier (-(x : ℤ))).continuous

/--
info: 'TaoFourierIdentity.integral_fourierPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms integral_fourierPolynomial
/--
info: 'TaoFourierIdentity.sixfold_fourier_count' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sixfold_fourier_count
/--
info: 'TaoFourierIdentity.representationCount_eq_fourier_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms representationCount_eq_fourier_integral
/--
info: 'TaoFourierIdentity.integrable_sixfold_fourier_count' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms integrable_sixfold_fourier_count

end TaoFourierIdentity

/-- The weighted count is exactly the integral in the finite circle-method formula. -/
theorem TaoFivePrimes.representationCount_fourier (x H : ℕ) :
    Integrable (TaoFivePrimes.representationIntegrand x H) AddCircle.haarAddCircle ∧
    (TaoFivePrimes.representationCount x H : ℂ) =
      ∫ α : AddCircle (1 : ℝ), TaoFivePrimes.representationIntegrand x H α
        ∂AddCircle.haarAddCircle := by
  constructor
  · exact TaoFourierIdentity.integrable_sixfold_fourier_count _ _ _ _ _ _
  · exact TaoFourierIdentity.representationCount_eq_fourier_integral x H

/--
info: 'TaoFivePrimes.representationCount_fourier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TaoFivePrimes.representationCount_fourier


/-!
The terminal numerical comparison for Tao's three-primes argument.

This theorem assumes both analytic estimates. It does not prove either estimate
or the unconditional number-theoretic milestone. The analytic estimates remain separate proof obligations.
-/

open MeasureTheory

open TaoFivePrimes

theorem final_major_minor_comparison (major minor : ℂ) (M : ℝ) (hM : 0 < M)
    (hMajor : (17 / 30 : ℝ) * M ≤ major.re)
    (hMinor : ‖minor‖ ≤ (8001 / 1000 : ℝ) * (1 / 25 : ℝ) * M) :
    (18497 / 75000 : ℝ) * M ≤ (major + minor).re ∧ 0 < (major + minor).re := by
  have hRe : -‖minor‖ ≤ minor.re := (abs_le.mp (Complex.abs_re_le_norm minor)).1
  have hLower : (18497 / 75000 : ℝ) * M ≤ (major + minor).re := by
    simp only [Complex.add_re]
    linarith
  refine ⟨hLower, ?_⟩
  linarith


/-- Explicit major and minor integral bounds suffice to make the actual count positive. -/
theorem solution (x H : ℕ) (E : Set (AddCircle (1 : ℝ)))
    (hE : MeasurableSet E) (M : ℝ) (hM : 0 < M)
    (hMajor : (17 / 30 : ℝ) * M ≤
      (∫ α in E, representationIntegrand x H α ∂AddCircle.haarAddCircle).re)
    (hMinor : ‖∫ α in Eᶜ, representationIntegrand x H α ∂AddCircle.haarAddCircle‖ ≤
      (8001 / 1000 : ℝ) * (1 / 25 : ℝ) * M) :
    (18497 / 75000 : ℝ) * M ≤ representationCount x H ∧
      0 < representationCount x H := by
  have h := final_major_minor_comparison _ _ M hM hMajor hMinor
  rw [integral_add_compl hE (representationCount_fourier x H).1,
    ← (representationCount_fourier x H).2, Complex.ofReal_re] at h
  exact h

/--
info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution
