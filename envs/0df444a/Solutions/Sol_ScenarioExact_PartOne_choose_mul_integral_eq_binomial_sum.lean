-- Prove2me | solution 1 for ScenarioExact.PartOne.choose_mul_integral_eq_binomial_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:25:01.490362+00:00
-- url     : https://prove2.me/submissions/325700ba-e79d-4a83-96ff-fcbe9a7b591e

import Mathlib

namespace P8582bd15

/-- Derivative of the partial binomial sum. -/
theorem deriv_partial (N : ℕ) (e : ℝ) :
    ∀ k : ℕ, k + 1 ≤ N →
      HasDerivAt (fun x : ℝ => ∑ i ∈ Finset.range (k + 1),
          (N.choose i : ℝ) * x ^ i * (1 - x) ^ (N - i))
        (-((N.choose (k + 1) : ℝ) * ((1 - e) ^ (N - (k + 1)) * (((k + 1 : ℕ) : ℝ) * e ^ k)))) e := by
  intro k
  induction k with
  | zero =>
    intro hN
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    simp only [zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, pow_zero,
      one_mul, Nat.sub_zero]
    have h : HasDerivAt (fun x : ℝ => (1 - x) ^ (m + 1))
        (((m + 1 : ℕ) : ℝ) * (1 - e) ^ (m + 1 - 1) * (-1)) e :=
      ((hasDerivAt_id' e).const_sub 1).pow (m + 1)
    refine h.congr_deriv ?_
    simp only [Nat.choose_one_right, Nat.add_sub_cancel]
    push_cast
    ring
  | succ k ih =>
    intro hN
    obtain ⟨m, rfl⟩ : ∃ m, N = k + 2 + m := ⟨N - (k + 2), by omega⟩
    have ih' := ih (by omega)
    have h1 : k + 2 + m - (k + 1) = m + 1 := by omega
    have h2 : k + 2 + m - (k + 1 + 1) = m := by omega
    rw [h1] at ih'
    rw [h2]
    have hc : ((k + 2 + m).choose (k + 1 + 1) : ℝ) * ((k + 1 + 1 : ℕ) : ℝ) =
        ((k + 2 + m).choose (k + 1) : ℝ) * ((m + 1 : ℕ) : ℝ) := by
      have := Nat.choose_succ_right_eq (k + 2 + m) (k + 1)
      rw [h1] at this
      exact_mod_cast this
    have hterm : HasDerivAt (fun x : ℝ => ((k + 2 + m).choose (k + 1) : ℝ) * x ^ (k + 1) *
        (1 - x) ^ (m + 1))
        (((k + 2 + m).choose (k + 1) : ℝ) * (((k + 1 : ℕ) : ℝ) * e ^ k) * (1 - e) ^ (m + 1) +
          ((k + 2 + m).choose (k + 1) : ℝ) * e ^ (k + 1) *
            (((m + 1 : ℕ) : ℝ) * (1 - e) ^ m * (-1))) e := by
      have a : HasDerivAt (fun x : ℝ => ((k + 2 + m).choose (k + 1) : ℝ) * x ^ (k + 1))
          (((k + 2 + m).choose (k + 1) : ℝ) * (((k + 1 : ℕ) : ℝ) * e ^ (k + 1 - 1))) e :=
        (hasDerivAt_pow (k + 1) e).const_mul _
      have b : HasDerivAt (fun x : ℝ => (1 - x) ^ (m + 1))
          (((m + 1 : ℕ) : ℝ) * (1 - e) ^ (m + 1 - 1) * (-1)) e :=
        ((hasDerivAt_id' e).const_sub 1).pow (m + 1)
      have c := a.mul b
      simp only [Nat.add_sub_cancel] at c
      exact c
    have hsum : HasDerivAt (fun x : ℝ => (∑ i ∈ Finset.range (k + 1),
          ((k + 2 + m).choose i : ℝ) * x ^ i * (1 - x) ^ (k + 2 + m - i)) +
          ((k + 2 + m).choose (k + 1) : ℝ) * x ^ (k + 1) * (1 - x) ^ (m + 1)) _ e :=
      ih'.add hterm
    have hfun : (fun x : ℝ => ∑ i ∈ Finset.range (k + 1 + 1),
          ((k + 2 + m).choose i : ℝ) * x ^ i * (1 - x) ^ (k + 2 + m - i)) =
        (fun x : ℝ => (∑ i ∈ Finset.range (k + 1),
          ((k + 2 + m).choose i : ℝ) * x ^ i * (1 - x) ^ (k + 2 + m - i)) +
          ((k + 2 + m).choose (k + 1) : ℝ) * x ^ (k + 1) * (1 - x) ^ (m + 1)) := by
      funext x
      rw [Finset.sum_range_succ, h1]
    rw [hfun]
    refine hsum.congr_deriv ?_
    push_cast at hc ⊢
    linear_combination ((1 - e) ^ m * e ^ (k + 1)) * hc

end P8582bd15

theorem solution {d N : ℕ} (hd : 1 ≤ d) (hN : d ≤ N) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (N.choose d : ℝ) * ∫ α in ε..1, (1 - α) ^ (N - d) * ((d : ℝ) * α ^ (d - 1)) =
      ∑ i ∈ Finset.range d, (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set F : ℝ → ℝ := fun x => ∑ i ∈ Finset.range (k + 1),
    (N.choose i : ℝ) * x ^ i * (1 - x) ^ (N - i) with hF
  have hderiv : ∀ x ∈ Set.uIcc ε 1, HasDerivAt (fun x => -F x)
      ((N.choose (k + 1) : ℝ) * ((1 - x) ^ (N - (k + 1)) * (((k + 1 : ℕ) : ℝ) * x ^ k))) x := by
    intro x _
    have h := (P8582bd15.deriv_partial N x k hN).neg
    rw [neg_neg] at h
    exact h
  have hint : IntervalIntegrable (fun x : ℝ =>
      (N.choose (k + 1) : ℝ) * ((1 - x) ^ (N - (k + 1)) * (((k + 1 : ℕ) : ℝ) * x ^ k)))
      MeasureTheory.volume ε 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hF1 : F 1 = 0 := by
    simp only [hF]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    have : N - i ≠ 0 := by omega
    simp [this]
  show -F 1 - -F ε = F ε
  rw [hF1]
  ring
