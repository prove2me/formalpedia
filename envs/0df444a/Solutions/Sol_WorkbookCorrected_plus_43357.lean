-- Prove2me | solution 1 for WorkbookCorrected.plus_43357
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:08:06.19877+00:00
-- url     : https://prove2.me/submissions/bf59526c-ed6a-4a3e-8e4b-241d97819c14

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Filter
open scoped Topology
private lemma step (t x : ℝ) (ht : 1 ≤ t) (hx : 0 ≤ x) (hb : t*x ≤ 1/2) :
    0 ≤ t*x^2/(1+(t+1)*x) ∧
    (t+1)*(t*x^2/(1+(t+1)*x)) ≤ (1/2)*(t*x) := by
  have ht0 : 0 < t := by linarith
  have hd : 0 < 1+(t+1)*x := by positivity
  have he : (t*x^2/(1+(t+1)*x))*(1+(t+1)*x)=t*x^2 := div_mul_cancel₀ _ (ne_of_gt hd)
  have hx1 : (t+1)*x ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht) hx]
  have hm := mul_nonneg (show 0 ≤ t*x by positivity) (sub_nonneg.mpr hx1)
  constructor
  · positivity
  · apply (mul_le_mul_iff_left₀ hd).mp
    nlinarith only [hm,congrArg (fun z : ℝ => (t+1)*z) he]

theorem solution (x : ℕ → ℝ) (h1 : x 1=1/2)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+1)=(n:ℝ)*x n^2/(1+((n:ℝ)+1)*x n)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |(n:ℝ)*x n| < ε := by
  have hb : ∀ n : ℕ, 0 ≤ x (n+1) ∧ ((n:ℝ)+1)*x (n+1) ≤ 1/2 ∧
      ((n:ℝ)+1)*x (n+1) ≤ (1/2:ℝ)^n := by
    intro n
    induction n with
    | zero => rw [h1]; norm_num
    | succ n ih =>
      have hh := step ((n:ℝ)+1) (x (n+1)) (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) ih.1 ih.2.1
      rw [show n+1+1=(n+1)+1 by omega,h (n+1) (by omega)]
      push_cast
      refine ⟨hh.1,by linarith [hh.2,ih.2.1],?_⟩
      calc
        ((n:ℝ)+1+1)*(((n:ℝ)+1)*x (n+1)^2/(1+((n:ℝ)+1+1)*x (n+1))) ≤ (1/2)*(((n:ℝ)+1)*x (n+1)) := hh.2
        _ ≤ (1/2)*(1/2:ℝ)^n := mul_le_mul_of_nonneg_left ih.2.2 (by norm_num)
        _ = (1/2:ℝ)^(n+1) := by rw [pow_succ]; ring
  have hp : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  intro ε hε
  obtain ⟨K,hK⟩ := (Metric.tendsto_atTop.mp hp) ε hε
  refine ⟨K+1,?_⟩
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m : ℕ, n=m+1 := ⟨n-1,by omega⟩
  have hh := hK m (by omega)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)] at hh
  push_cast
  rw [abs_of_nonneg (mul_nonneg (by positivity) (hb m).1)]
  exact lt_of_le_of_lt (hb m).2.2 hh
example : (∀ (x : ℕ → ℝ) (h1 : x 1=1/2)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+1)=(n:ℝ)*x n^2/(1+((n:ℝ)+1)*x n)),
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |(n:ℝ)*x n| < ε) := @solution
#print axioms solution
