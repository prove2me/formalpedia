-- Prove2me | solution 1 for UnderstandingML.online_perceptron_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T13:22:29.733158+00:00
-- url     : https://prove2.me/submissions/40f55148-bedb-41aa-8fa2-e29296e24698


import Definitions.Def_UnderstandingML_Online

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

theorem perceptronRounds_succ {d : ℕ} (x : ℕ → Vec d) (y : ℕ → ℝ) (n : ℕ) :
    perceptronRounds x y (n + 1) =
      if y n * ⟪onlinePerceptron x y n, x n⟫_ℝ ≤ 0 then insert n (perceptronRounds x y n)
      else perceptronRounds x y n := by
  unfold perceptronRounds
  rw [Finset.range_add_one, Finset.filter_insert]

theorem perceptron_invariants {d : ℕ} (T : ℕ) (x : ℕ → Vec d) (y : ℕ → ℝ)
    (hy : ∀ t, y t = 1 ∨ y t = -1) (R : ℝ) (hR : ∀ t < T, ‖x t‖ ≤ R) (wstar : Vec d) :
    ∀ n ≤ T, ‖onlinePerceptron x y n‖ ^ 2 ≤ R ^ 2 * (perceptronRounds x y n).card ∧
      ⟪wstar, onlinePerceptron x y n⟫_ℝ =
        ∑ t ∈ perceptronRounds x y n, y t * ⟪wstar, x t⟫_ℝ := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [onlinePerceptron, perceptronRounds]
  | succ n ih =>
    intro hn
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hnT : n < T := by omega
    rw [perceptronRounds_succ]
    by_cases hc : y n * ⟪onlinePerceptron x y n, x n⟫_ℝ ≤ 0
    · have hnot : n ∉ perceptronRounds x y n := by
        simp [perceptronRounds]
      simp only [onlinePerceptron, hc, if_true]
      rw [Finset.card_insert_of_notMem hnot, Finset.sum_insert hnot]
      have hy2 : y n ^ 2 = 1 := by rcases hy n with h | h <;> simp [h]
      have hxn : ‖x n‖ ^ 2 ≤ R ^ 2 := by
        have h0 := norm_nonneg (x n)
        have := hR n hnT
        nlinarith
      refine ⟨?_, ?_⟩
      · rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hy2]
        push_cast
        nlinarith
      · rw [inner_add_right, inner_smul_right, ih2]
        ring
    · simp only [onlinePerceptron, hc, if_false]
      exact ⟨ih1, ih2⟩

theorem perceptron_count_algebra (m L a : ℝ) (hm : 0 ≤ m) (hL : 0 ≤ L) (ha : 0 ≤ a)
    (h : m ≤ L + a * Real.sqrt m) : m ≤ L + a * Real.sqrt L + a ^ 2 := by
  set s := Real.sqrt m with hs
  set l := Real.sqrt L with hl
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hl0 : 0 ≤ l := Real.sqrt_nonneg _
  have hss : s ^ 2 = m := Real.sq_sqrt hm
  have hll : l ^ 2 = L := Real.sq_sqrt hL
  have hsl : s ≤ l + a := by
    rcases le_or_gt s (l + a) with h | h
    · exact h
    · nlinarith
  nlinarith

theorem online_perceptron_bound {d : ℕ} (T : ℕ) (x : ℕ → Vec d) (y : ℕ → ℝ)
    (hy : ∀ t, y t = 1 ∨ y t = -1) (R : ℝ) (hR : ∀ t < T, ‖x t‖ ≤ R) (wstar : Vec d) :
    ((perceptronRounds x y T).card : ℝ) ≤
      (∑ t ∈ perceptronRounds x y T, max 0 (1 - y t * ⟪wstar, x t⟫_ℝ)) +
        R * ‖wstar‖ * Real.sqrt (∑ t ∈ perceptronRounds x y T, max 0 (1 - y t * ⟪wstar, x t⟫_ℝ)) +
        R ^ 2 * ‖wstar‖ ^ 2 ∧
    ((∀ t < T, 1 ≤ y t * ⟪wstar, x t⟫_ℝ) →
      ((perceptronRounds x y T).card : ℝ) ≤ R ^ 2 * ‖wstar‖ ^ 2) := by
  obtain ⟨h1, h2⟩ := perceptron_invariants T x y hy R hR wstar T le_rfl
  set M := perceptronRounds x y T with hM
  set L := ∑ t ∈ M, max 0 (1 - y t * ⟪wstar, x t⟫_ℝ) with hLdef
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun _ _ ↦ le_max_left _ _)
  have main : (M.card : ℝ) ≤ L + R * ‖wstar‖ * Real.sqrt L + R ^ 2 * ‖wstar‖ ^ 2 := by
    rcases M.eq_empty_or_nonempty with hE | hNE
    · have hL' : L = 0 := by rw [hLdef, hE]; simp
      rw [hE, hL']
      simp
      positivity
    · obtain ⟨t0, ht0⟩ := hNE
      have ht0T : t0 < T := by
        have := Finset.mem_filter.1 ht0
        exact Finset.mem_range.1 this.1
      have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR t0 ht0T)
      have hlow : (M.card : ℝ) - L ≤ ⟪wstar, onlinePerceptron x y T⟫_ℝ := by
        rw [h2, hLdef, Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_le_sum
        intro t _
        push_cast
        have := le_max_right 0 (1 - y t * ⟪wstar, x t⟫_ℝ)
        linarith
      have hcs := real_inner_le_norm wstar (onlinePerceptron x y T)
      have hwT : ‖onlinePerceptron x y T‖ ≤ R * Real.sqrt M.card := by
        rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hR0, ← Real.sqrt_mul (sq_nonneg _)]
        exact Real.sqrt_le_sqrt h1
      have hstep : (M.card : ℝ) ≤ L + (R * ‖wstar‖) * Real.sqrt M.card := by
        have := mul_le_mul_of_nonneg_left hwT (norm_nonneg wstar)
        nlinarith
      have := perceptron_count_algebra (M.card) L (R * ‖wstar‖) (by positivity) hL0
        (by positivity) hstep
      nlinarith
  refine ⟨main, fun hsep ↦ ?_⟩
  have hL : L = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have htT : t < T := Finset.mem_range.1 (Finset.mem_filter.1 ht).1
    have := hsep t htT
    exact max_eq_left (by linarith)
  rw [hL] at main
  simpa using main

end UnderstandingML

open UnderstandingML in
theorem solution {d : ℕ} (T : ℕ) (x : ℕ → Vec d) (y : ℕ → ℝ)
    (hy : ∀ t, y t = 1 ∨ y t = -1) (R : ℝ) (hR : ∀ t < T, ‖x t‖ ≤ R) (wstar : Vec d) :
    ((perceptronRounds x y T).card : ℝ) ≤
      (∑ t ∈ perceptronRounds x y T, max 0 (1 - y t * ⟪wstar, x t⟫_ℝ)) +
        R * ‖wstar‖ * Real.sqrt (∑ t ∈ perceptronRounds x y T, max 0 (1 - y t * ⟪wstar, x t⟫_ℝ)) +
        R ^ 2 * ‖wstar‖ ^ 2 ∧
    ((∀ t < T, 1 ≤ y t * ⟪wstar, x t⟫_ℝ) →
      ((perceptronRounds x y T).card : ℝ) ≤ R ^ 2 * ‖wstar‖ ^ 2) := by
  apply UnderstandingML.online_perceptron_bound <;> assumption
