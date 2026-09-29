-- Prove2me | solution 1 for TaoFivePrimes.reciprocal_primes_theta_partial_summation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T23:00:38.538626+00:00
-- url     : https://prove2.me/submissions/23958e3b-29a3-45eb-8403-823725f96c18

import Mathlib

open MeasureTheory

theorem solution (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) =
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ)) / (x * Real.log x) +
      ∫ t in Set.Ioc (2 : ℝ) x,
        (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) *
          (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) := by
  let c : ℕ → ℝ := fun n => if n.Prime then Real.log n else 0
  let f : ℝ → ℝ := fun t => (t * Real.log t)⁻¹
  let g : ℝ → ℝ := fun t => -(Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)
  have hpos (t : ℝ) (ht : 2 ≤ t) : 0 < t ∧ 0 < Real.log t :=
    ⟨by linarith, Real.log_pos (by linarith)⟩
  have hd (t : ℝ) (ht : 2 ≤ t) : HasDerivAt f (g t) t := by
    have ht0 := ne_of_gt (hpos t ht).1
    have hl0 := ne_of_gt (hpos t ht).2
    convert ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)).inv
      (mul_ne_zero ht0 hl0) using 1 <;>
      first | rfl | ((try dsimp [f, g]) <;> (try field_simp [ht0, hl0]) <;> ring)
  have hc0 : c 0 = 0 := by simp [c]
  have hc1 : c 1 = 0 := by simp [c]
  have hc (t : ℝ) : (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
      ∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) := by
    simp [Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter, c]
  have hsum : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n * c n) =
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ) := by
    rw [Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hnl : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
      simp only [c, hp, if_true, f]
      field_simp [hn0, hnl]
    · simp [c, hp]
  have hlogc : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc (2 : ℝ) x) :=
    continuousOn_id.log (fun t ht => ne_of_gt (hpos t ht.1).1)
  have hg : ContinuousOn g (Set.Icc (2 : ℝ) x) := by
    apply ((hlogc.add continuousOn_const).neg).div
      ((continuousOn_id.pow 2).mul (hlogc.pow 2))
    intro t ht
    exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt (hpos t ht.1).1))
      (pow_ne_zero 2 (ne_of_gt (hpos t ht.1).2))
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x, DifferentiableAt ℝ f t :=
    fun t ht => (hd t ht.1).differentiableAt
  have hint : IntegrableOn (deriv f) (Set.Icc (2 : ℝ) x) :=
    (hg.integrableOn_Icc).congr_fun (fun t ht => (hd t ht.1).deriv.symm) measurableSet_Icc
  have hab := sum_mul_eq_sub_integral_mul₁ c hc0 hc1 x hdiff hint
  rw [hsum, hc] at hab
  have hi : (∫ t in Set.Ioc (2 : ℝ) x, deriv f t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
      -(∫ t in Set.Ioc (2 : ℝ) x,
        (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) *
          (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ht.1.le).deriv, hc]
    dsimp [g]
    ring
  rw [hi] at hab
  simpa [f, div_eq_mul_inv, mul_comm, sub_neg_eq_add] using hab
