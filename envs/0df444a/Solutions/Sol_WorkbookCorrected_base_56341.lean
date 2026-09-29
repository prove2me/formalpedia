-- Prove2me | solution 1 for WorkbookCorrected.base_56341
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T13:06:26.05959+00:00
-- url     : https://prove2.me/submissions/3c964d08-986a-42b8-8540-a33e6311916d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma step_bound (t c u : ℝ) (ht : 1 ≤ t) (hc : 0 < c)
    (hu : 0 ≤ u) (hub : u ≤ c*t/(t+c+1)) :
    0 ≤ u+u^2/t^2 ∧ u+u^2/t^2 ≤ c*(t+1)/(t+c+2) := by
  have ht0 : 0 < t := by linarith
  have hd1 : 0 < t+c+1 := by linarith
  have hd2 : 0 < t+c+2 := by linarith
  have hb0 : 0 ≤ c*t/(t+c+1) := by positivity
  constructor
  · positivity
  · have hs : u^2 ≤ (c*t/(t+c+1))^2 := by nlinarith
    have hsdiv := div_le_div_of_nonneg_right hs (sq_nonneg t)
    have hid : c*(t+1)/(t+c+2) -
        (c*t/(t+c+1) + (c*t/(t+c+1))^2/t^2) =
        c*(t+1)/((t+c+1)^2*(t+c+2)) := by
      field_simp
      <;> ring
    have hp : 0 ≤ c*(t+1)/((t+c+1)^2*(t+c+2)) := by positivity
    linarith

theorem solution (x : ℕ → ℝ) (h0 : 0 < x 1) (h1 : x 1 < 1)
    (hrec : ∀ n : ℕ, 1 ≤ n → x (n+1) = x n + (x n)^2/(n:ℝ)^2) :
    ∃ M : ℝ, ∀ n : ℕ, 1 ≤ n → x n < M := by
  let c : ℝ := 2*x 1/(1-x 1)
  have ha : 0 < 1-x 1 := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hc_eq : c*(1-x 1) = 2*x 1 := by dsimp [c]; field_simp
  have hinit : x 1 = c/(c+2) := by
    apply (eq_div_iff (ne_of_gt (by linarith : 0 < c+2))).2
    nlinarith only [hc_eq]
  have hb : ∀ n : ℕ, 0 ≤ x (n+1) ∧
      x (n+1) ≤ c*((n:ℝ)+1)/((n:ℝ)+c+2) := by
    intro n
    induction n with
    | zero =>
      norm_num only [Nat.cast_zero, zero_add, mul_one]
      exact ⟨le_of_lt h0, le_of_eq hinit⟩
    | succ n ih =>
      have ht : (1:ℝ) ≤ (n:ℝ)+1 := by
        have hn0 : 0 ≤ (n:ℝ) := by positivity
        linarith
      have hub : x (n+1) ≤ c*((n:ℝ)+1)/(((n:ℝ)+1)+c+1) := by
        convert ih.2 using 1 <;> ring
      have hs := step_bound ((n:ℝ)+1) c (x (n+1)) ht hc ih.1 hub
      rw [hrec (n+1) (by omega)]
      convert hs using 1 <;> push_cast <;> ring
  refine ⟨c+1, ?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ k =>
    have hd : 0 < (k:ℝ)+c+2 := by positivity
    have hu : c*((k:ℝ)+1)/((k:ℝ)+c+2) < c+1 := by
      apply (div_lt_iff₀ hd).2
      nlinarith [sq_nonneg c, (show 0 ≤ (k:ℝ) by positivity)]
    exact lt_of_le_of_lt (hb k).2 hu
example : (∀ (x : ℕ → ℝ) (h0 : 0 < x 1) (h1 : x 1 < 1)
    (hrec : ∀ n : ℕ, 1 ≤ n → x (n+1) = x n + (x n)^2/(n:ℝ)^2),
    ∃ M : ℝ, ∀ n : ℕ, 1 ≤ n → x n < M) := @solution
#print axioms solution
