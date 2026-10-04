-- Prove2me | solution 1 for TaoFivePrimes.representationCount_eq_smoothed_integral
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-07T04:04:35.415326+00:00
-- url     : https://prove2.me/submissions/8caa05a3-d17d-42bc-9fb4-b423c2104e56

import Definitions.Def_TaoFivePrimes_FourierRepresentation
import Definitions.Def_TaoFivePrimes_SmoothedSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum


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

open MeasureTheory TaoFivePrimes
open scoped BigOperators ArithmeticFunction.vonMangoldt
namespace TaoGlobalL2Proof
theorem smoothedSum_eq_sum {η : ℝ → ℝ} {q : ℕ} {x : ℝ}
    (hx : 1 ≤ x) (hη : ∀ t : ℝ, 1 < t → η t = 0) (α : AddCircle (1 : ℝ)) :
    smoothedSum η q x α =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        if n.Coprime q then
          (η ((n : ℝ) / x) * Λ n : ℝ) • fourier (n : ℤ) α else 0 := by
  unfold smoothedSum
  apply tsum_eq_sum
  intro n hn
  have hnx : x < (n : ℝ) := by
    apply lt_of_not_ge
    intro h
    exact hn (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor h)))
  have harg : 1 < (n : ℝ) / x :=
    (lt_div_iff₀ (lt_of_lt_of_le zero_lt_one hx)).2 (by simpa using hnx)
  simp [hη _ harg]


end TaoGlobalL2Proof




namespace TaoFivePrimes

theorem eta0_nonneg (t : ℝ) : 0 ≤ eta0 t := by
  unfold eta0
  split_ifs
  · exact mul_nonneg (by norm_num) (le_max_left _ _)
  · exact le_rfl

theorem eta0_eq_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) : eta0 t = 0 := by
  have hlog : Real.log 2 ≤ Real.log (2 * t) :=
    Real.log_le_log (by norm_num) (by linarith)
  have habs := le_abs_self (Real.log (2 * t))
  unfold eta0
  rw [if_pos (by linarith), max_eq_left (by linarith), mul_zero]

theorem eta1_nonneg (t : ℝ) : 0 ≤ eta1 t := le_max_left _ _

theorem eta1_le_one (t : ℝ) : eta1 t ≤ 1 := by
  have hd : 0 ≤ Metric.infDist t (Set.Icc (1 / 5 : ℝ) (4 / 5)) :=
    Metric.infDist_nonneg
  exact max_le (by norm_num) (by linarith)

theorem eta1_eq_one {t : ℝ} (ht : t ∈ Set.Icc (1 / 5 : ℝ) (4 / 5)) :
    eta1 t = 1 := by
  unfold eta1
  rw [Metric.infDist_zero_of_mem ht]
  norm_num

theorem eta1_eq_zero_of_nine_tenths_le {t : ℝ} (ht : 9 / 10 ≤ t) : eta1 t = 0 := by
  have hs : (Set.Icc (1 / 5 : ℝ) (4 / 5)).Nonempty := ⟨1 / 2, by norm_num⟩
  have hd : t - 4 / 5 ≤ Metric.infDist t (Set.Icc (1 / 5 : ℝ) (4 / 5)) := by
    apply (Metric.le_infDist hs).2
    intro y hy
    rw [Real.dist_eq]
    exact (sub_le_sub_left hy.2 t).trans (le_abs_self _)
  unfold eta1
  exact max_eq_left (by linarith)

theorem eta1_eq_zero_of_le_one_tenth {t : ℝ} (ht : t ≤ 1 / 10) : eta1 t = 0 := by
  have hs : (Set.Icc (1 / 5 : ℝ) (4 / 5)).Nonempty := ⟨1 / 2, by norm_num⟩
  have hd : 1 / 5 - t ≤ Metric.infDist t (Set.Icc (1 / 5 : ℝ) (4 / 5)) := by
    apply (Metric.le_infDist hs).2
    intro y hy
    rw [Real.dist_eq, abs_sub_comm]
    exact (sub_le_sub_right hy.1 t).trans (le_abs_self _)
  unfold eta1
  exact max_eq_left (by linarith)

end TaoFivePrimes





open MeasureTheory TaoFourierIdentity
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

/-- The first finite prime sum is the already defined smoothed von Mangoldt sum. -/
theorem first_prime_sum_eq_smoothedSum (x : ℕ) (hx : 1 ≤ x)
    (α : AddCircle (1 : ℝ)) :
    fourierPolynomial (Finset.range (x + 1))
      (fun n ↦ (siftedVonMangoldt x n * eta1 ((n : ℝ) / x) : ℝ))
      (fun n ↦ (n : ℤ)) α =
    smoothedSum eta1 (primorial (Nat.sqrt x)) x α := by
  rw [TaoGlobalL2Proof.smoothedSum_eq_sum (by exact_mod_cast hx)
    (fun t ht ↦ eta1_eq_zero_of_nine_tenths_le (by linarith))]
  simp only [Nat.floor_natCast, fourierPolynomial]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : n.Coprime (primorial (Nat.sqrt x))
  · simp only [siftedVonMangoldt, if_pos hc, Complex.real_smul, Complex.ofReal_mul]
    ring
  · simp only [siftedVonMangoldt, if_neg hc, zero_mul, Complex.ofReal_zero]

/-- The small prime sum has real scale `x / 1000` and the corresponding floor sieve. -/
theorem third_prime_sum_eq_smoothedSum (x : ℕ) (hx : 1000 ≤ x)
    (α : AddCircle (1 : ℝ)) :
    fourierPolynomial (Finset.range (x / 1000 + 1))
      (fun n ↦ (siftedVonMangoldt (x / 1000) n * eta0 (1000 * (n : ℝ) / x) : ℝ))
      (fun n ↦ (n : ℤ)) α =
    smoothedSum eta0 (primorial (Nat.sqrt (x / 1000))) ((x : ℝ) / 1000) α := by
  have hxR : (1000 : ℝ) ≤ x := by exact_mod_cast hx
  rw [TaoGlobalL2Proof.smoothedSum_eq_sum (by linarith)
    (fun t ht ↦ eta0_eq_zero_of_one_le ht.le)]
  rw [show ⌊(x : ℝ) / 1000⌋₊ = x / 1000 from Nat.floor_div_eq_div x 1000]
  unfold fourierPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : n.Coprime (primorial (Nat.sqrt (x / 1000)))
  · have hscale : (n : ℝ) / ((x : ℝ) / 1000) = 1000 * (n : ℝ) / x := by
      rw [div_div_eq_mul_div, mul_comm]
    simp only [siftedVonMangoldt, if_pos hc, Complex.real_smul, Complex.ofReal_mul,
      hscale]
    ring
  · simp only [siftedVonMangoldt, if_neg hc, zero_mul, Complex.ofReal_zero]

/-- Equation (8.11) expressed with the published infinite-sum notation. -/
theorem representationCount_eq_smoothed_integral_local (x H : ℕ) (hx : 1000 ≤ x) :
    (representationCount x H : ℂ) =
      ∫ α : AddCircle (1 : ℝ),
        smoothedSum eta1 (primorial (Nat.sqrt x)) x α ^ 2 *
        smoothedSum eta0 (primorial (Nat.sqrt (x / 1000))) ((x : ℝ) / 1000) α *
        fourierPolynomial (Finset.Icc 1 (H / 3)) (fun _ ↦ 1)
          (fun n ↦ (n : ℤ)) α ^ 3 * fourier (-(x : ℤ)) α
        ∂AddCircle.haarAddCircle := by
  rw [(representationCount_fourier x H).2]
  apply integral_congr_ae
  filter_upwards [] with α
  unfold representationIntegrand
  rw [first_prime_sum_eq_smoothedSum x (by omega), third_prime_sum_eq_smoothedSum x hx]


end TaoFivePrimes

open TaoFivePrimes TaoFourierIdentity

theorem solution (x H : ℕ) (hx : 1000 ≤ x) :
    (representationCount x H : ℂ) =
      ∫ α : AddCircle (1 : ℝ),
        smoothedSum eta1 (primorial (Nat.sqrt x)) x α ^ 2 *
        smoothedSum eta0 (primorial (Nat.sqrt (x / 1000))) ((x : ℝ) / 1000) α *
        fourierPolynomial (Finset.Icc 1 (H / 3)) (fun _ ↦ 1)
          (fun n ↦ (n : ℤ)) α ^ 3 * fourier (-(x : ℤ)) α
        ∂AddCircle.haarAddCircle := by
  exact representationCount_eq_smoothed_integral_local x H hx

/--
info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution
