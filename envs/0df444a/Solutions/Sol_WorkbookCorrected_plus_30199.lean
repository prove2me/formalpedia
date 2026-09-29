-- Prove2me | solution 1 for WorkbookCorrected.plus_30199
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:48:40.402073+00:00
-- url     : https://prove2.me/submissions/325c70e0-0ffc-4e8e-9f5a-59f39c06769e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Filter
open scoped Topology

theorem solution (x : ℕ → ℝ) (hx : 0 < x 1 ∧ x 1 < 1)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+1)=x n*(2-x n)) :
    (∀ n : ℕ, 1 ≤ n → 0 < x n ∧ x n < 1) ∧
    (∀ n : ℕ, 1 ≤ n → x n < x (n+1)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |x n-1| < ε) := by
  let q := 1-x 1
  have hq0 : 0 ≤ q := by dsimp [q]; linarith [hx.2]
  have hq1 : q < 1 := by dsimp [q]; linarith [hx.1]
  have hb : ∀ n : ℕ, x 1 ≤ x (n+1) ∧ x (n+1) < 1 ∧ 1-x (n+1) ≤ q^n := by
    intro n
    induction n with
    | zero => norm_num; exact ⟨hx.2,by linarith [hx.1]⟩
    | succ n ih =>
      have hp : 0 < x (n+1) := lt_of_lt_of_le hx.1 ih.1
      have hg := mul_pos hp (sub_pos.mpr ih.2.1)
      have hs := sq_pos_of_pos (sub_pos.mpr ih.2.1)
      have hc := mul_nonneg (show 0 ≤ x (n+1)-x 1 by linarith [ih.1])
        (show 0 ≤ 1-x (n+1) by linarith [ih.2.1])
      have he : 1-x (n+1)*(2-x (n+1)) ≤ q*(1-x (n+1)) := by
        dsimp [q]
        nlinarith only [hc]
      rw [show n+1+1=(n+1)+1 by omega, h (n+1) (by omega)]
      refine ⟨by nlinarith only [hg,ih.1],by nlinarith only [hs],?_⟩
      calc
        1-x (n+1)*(2-x (n+1)) ≤ q*(1-x (n+1)) := he
        _ ≤ q*q^n := mul_le_mul_of_nonneg_left ih.2.2 hq0
        _ = q^(n+1) := by rw [pow_succ]; ring
  have hi : ∀ n : ℕ, 1 ≤ n → 0 < x n ∧ x n < 1 := by
    intro n hn
    obtain ⟨m,rfl⟩ : ∃ m : ℕ, n=m+1 := ⟨n-1,by omega⟩
    exact ⟨lt_of_lt_of_le hx.1 (hb m).1,(hb m).2.1⟩
  refine ⟨hi,?_,?_⟩
  · intro n hn
    have hh := hi n hn
    rw [h n hn]
    nlinarith only [mul_pos hh.1 (sub_pos.mpr hh.2)]
  · have hp : Tendsto (fun n : ℕ => q^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    intro ε hε
    obtain ⟨K,hK⟩ := (Metric.tendsto_atTop.mp hp) ε hε
    refine ⟨K+1,?_⟩
    intro n hn
    obtain ⟨m,rfl⟩ : ∃ m : ℕ, n=m+1 := ⟨n-1,by omega⟩
    have hh := hK m (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hq0 m)] at hh
    rw [abs_of_nonpos (by linarith [(hb m).2.1] : x (m+1)-1 ≤ 0)]
    have he := lt_of_le_of_lt (hb m).2.2 hh
    linarith only [he]
example : (∀ (x : ℕ → ℝ) (hx : 0 < x 1 ∧ x 1 < 1)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+1)=x n*(2-x n)),
    (∀ n : ℕ, 1 ≤ n → 0 < x n ∧ x n < 1) ∧
    (∀ n : ℕ, 1 ≤ n → x n < x (n+1)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |x n-1| < ε)) := @solution
#print axioms solution
