-- Prove2me | solution 1 for WorkbookCorrected.plus_61506
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:36:25.373731+00:00
-- url     : https://prove2.me/submissions/a52bdae8-65fd-4f0c-b714-ec71b6fd0fd9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Filter
open scoped Topology

theorem solution (a : ℕ → ℝ) (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=Real.sqrt (6-2*(a n)^2)) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → a n=c := by
  have he : ∀ n : ℕ, 1 ≤ n → (a (n+1))^2=6-2*(a n)^2 := by
    intro n hn
    have hp : 0 < Real.sqrt (6-2*(a n)^2) := by rw [← h n hn]; exact ha (n+1) (by omega)
    have hh := Real.sq_sqrt (le_of_lt (Real.sqrt_pos.mp hp))
    rw [← h n hn] at hh
    exact hh
  have hb : ∀ n : ℕ, 1 ≤ n → |(a n)^2-2| ≤ 2 := by
    intro n hn
    have hh := he n hn
    rw [abs_le]
    constructor <;> nlinarith only [hh,sq_nonneg (a n),sq_nonneg (a (n+1))]
  have hg : ∀ k : ℕ, ∀ n : ℕ, 1 ≤ n → |(a n)^2-2| ≤ 2*(1/2:ℝ)^k := by
    intro k
    induction k with
    | zero => simpa using hb
    | succ k ih =>
      intro n hn
      have hh := ih (n+1) (by omega)
      have hid : (a (n+1))^2-2 = -2*((a n)^2-2) := by linarith only [he n hn]
      rw [hid,abs_mul] at hh
      norm_num at hh
      have hpw : 2*(1/2:ℝ)^(k+1)=(1/2:ℝ)^k := by rw [pow_succ]; ring
      rw [hpw]
      exact hh
  have hp : Tendsto (fun k : ℕ => 2*(1/2:ℝ)^k) atTop (𝓝 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul (2:ℝ)
    simpa using hh
  refine ⟨Real.sqrt 2,?_⟩
  intro n hn
  have hz : |(a n)^2-2| ≤ 0 := ge_of_tendsto' hp (fun k => hg k n hn)
  have hsq : (a n)^2=2 := by have hh := abs_le.mp hz; linarith
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have ha0 := ha n hn
  nlinarith only [hsq,hs,hs0,ha0]
example : (∀ (a : ℕ → ℝ) (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=Real.sqrt (6-2*(a n)^2)),
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → a n=c) := @solution
#print axioms solution
