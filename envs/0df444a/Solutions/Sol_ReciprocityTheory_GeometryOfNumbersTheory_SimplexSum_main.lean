-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:28:43.567289+00:00
-- url     : https://prove2.me/submissions/e7e41a1b-a297-46a1-912d-62a7dab122ea

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_SimplexSumSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SimplexSum_sum_bounds
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SimplexSum_S_zero
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SimplexSum_S_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Filter Asymptotics Finset
open ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum
namespace ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum
theorem _root_.solution (j : ℕ) : ∀ i : ℕ, (fun n : ℕ => S i j n / ((i.factorial : ℝ) * (j.factorial : ℝ)) -
      (n : ℝ) ^ (i + j + 1) / ((i + j + 1).factorial : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (i + j) := by
  induction j with
  | zero =>
    intro i
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    obtain ⟨hb1, hb2⟩ := sum_bounds i n
    simp only [S_zero, Nat.factorial_zero, Nat.cast_one, mul_one, add_zero]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) ^ i), one_mul,
      Nat.factorial_succ]
    push_cast
    have hf : (1 : ℝ) ≤ i.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)
    have hi : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
    have hp : (0 : ℝ) ≤ (n : ℝ) ^ i := by positivity
    set T := ∑ a ∈ range (n + 1), (a : ℝ) ^ i
    have key : T / i.factorial - (n : ℝ) ^ (i + 1) / (((i : ℝ) + 1) * i.factorial) =
        (((i : ℝ) + 1) * T - (n : ℝ) ^ (i + 1)) / (((i : ℝ) + 1) * i.factorial) := by
      field_simp
    rw [key, abs_le]
    constructor
    · have : 0 ≤ (((i : ℝ) + 1) * T - (n : ℝ) ^ (i + 1)) / (((i : ℝ) + 1) * i.factorial) :=
        div_nonneg (by linarith) (by positivity)
      linarith
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hp hi) (by linarith : (0:ℝ) ≤ i.factorial - 1)]
  | succ j ih =>
    intro i
    have h1 := ((isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul (ih i)).const_mul_left (1 / ((j : ℝ) + 1))
    have h2 := (ih (i + 1)).const_mul_left (((i : ℝ) + 1) / ((j : ℝ) + 1))
    have h2' : (fun x : ℕ => ((i : ℝ) + 1) / ((j : ℝ) + 1) *
        (S (i + 1) j x / (((i + 1).factorial : ℝ) * (j.factorial : ℝ)) -
          (x : ℝ) ^ (i + 1 + j + 1) / ((i + 1 + j + 1).factorial : ℝ))) =O[atTop]
        fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (i + j) := h2.congr_right (fun n => by ring)
    refine (h1.sub h2').congr' ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      dsimp only
      rw [S_succ]
      rw [show i + (j + 1) + 1 = i + j + 1 + 1 by ring, show i + 1 + j + 1 = i + j + 1 + 1 by ring,
        Nat.factorial_succ (i + j + 1), Nat.factorial_succ j, Nat.factorial_succ i]
      push_cast
      field_simp
      ring
    · refine Eventually.of_forall fun n => ?_
      dsimp only
      ring
end ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum
