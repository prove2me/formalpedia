-- Prove2me | solution 1 for WorkbookCorrected.plus_25846
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:39:40.354919+00:00
-- url     : https://prove2.me/submissions/c7187478-24bc-4aec-996b-043aabcead53

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Filter
open scoped Topology
private lemma shrink (r x : ℝ) (hr : 1/2 ≤ r) (hr2 : r^2+r=1) (hx : 0≤x) :
    |1/(1+x)-r| ≤ (2/3)*|x-r| := by
  have hd : 3/2 ≤ (1+x)*(1+r) := by nlinarith [mul_nonneg hx (by linarith : 0≤r)]
  have hp : 0<(1+x)*(1+r) := by linarith
  have he : 1/(1+x)-r = -(x-r)/((1+x)*(1+r)) := by
    field_simp
    nlinarith [hr2]
  rw [he, abs_div, abs_neg, abs_of_pos hp]
  have hh := div_le_div_of_nonneg_left (abs_nonneg (x-r)) (by norm_num : (0:ℝ)<3/2) hd
  calc
    |x-r|/((1+x)*(1+r)) ≤ |x-r|/(3/2) := hh
    _ = (2/3)*|x-r| := by ring

theorem solution (x : ℕ → ℝ) (h1 : x 1 = 1)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+1) = 1/(1+x n)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |x n - (Real.sqrt 5-1)/2| < ε := by
  let r := (Real.sqrt 5-1)/2
  have hs := Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
  have hs0 := Real.sqrt_nonneg (5:ℝ)
  have hr : 1/2 ≤ r := by dsimp [r]; nlinarith
  have hr1 : r≤1 := by dsimp [r]; nlinarith
  have hr2 : r^2+r=1 := by dsimp [r]; nlinarith
  have hb : ∀ n : ℕ, 0≤x (n+1) ∧ |x (n+1)-r|≤(2/3:ℝ)^n := by
    intro n
    induction n with
    | zero =>
      rw [h1]
      norm_num
      rw [abs_of_nonneg (by linarith : 0≤1-r)]
      linarith
    | succ n ih =>
      rw [show n+1+1=(n+1)+1 by omega, h (n+1) (by omega)]
      constructor
      · exact le_of_lt (one_div_pos.mpr (by linarith [ih.1]))
      · calc
          |1/(1+x (n+1))-r| ≤ (2/3)*|x (n+1)-r| := shrink r _ hr hr2 ih.1
          _ ≤ (2/3)*(2/3:ℝ)^n := mul_le_mul_of_nonneg_left ih.2 (by norm_num)
          _ = (2/3:ℝ)^(n+1) := by rw [pow_succ]; ring
  have hp : Tendsto (fun n : ℕ => (2/3:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  intro ε hε
  obtain ⟨K,hK⟩ := (Metric.tendsto_atTop.mp hp) ε hε
  refine ⟨K+1, ?_⟩
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m : ℕ, n=m+1 := ⟨n-1, by omega⟩
  have hh := hK m (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hh
  exact lt_of_le_of_lt (hb m).2 hh
example : (∀ (x : ℕ → ℝ) (h1 : x 1 = 1)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+1) = 1/(1+x n)),
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |x n - (Real.sqrt 5-1)/2| < ε) := @solution
#print axioms solution
