-- Prove2me | solution 4 for PiIrrationality.openai_bound_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T16:47:16.755839+00:00
-- url     : https://prove2.me/submissions/c55ac495-2c46-4822-b765-c5ed4b39b63e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_rational_approximation_lower_bound
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Definitions.Def_PiIrrationality_UpperBound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution : PiIrrationality.UpperBound (2 : ℝ) := by
  intro eps heps
  let nu : ℝ := 2 + eps / 2
  have hnu : 2 < nu := by
    dsimp [nu]
    linarith
  obtain ⟨Q, hQ, happrox⟩ :=
    OAI.PiExponent.rational_approximation_lower_bound nu hnu
  refine ⟨max Q 2, ?_⟩
  intro p q hqpos hqmax
  have hq : Q ≤ q := (le_max_left Q 2).trans hqmax
  have hq2 : 2 ≤ q := (le_max_right Q 2).trans hqmax
  have hq1 : (1 : ℝ) < (q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hq2)
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hpow : (q : ℝ) ^ (-(2 + eps)) < (q : ℝ) ^ (-nu) := by
    apply Real.rpow_lt_rpow_of_exponent_lt hq1
    dsimp [nu]
    linarith
  calc
    1 / (q : ℝ) ^ ((2 : ℝ) + eps) =
        (q : ℝ) ^ (-(2 + eps)) := by
      rw [Real.rpow_neg hq0]
      simp only [one_div]
    _ < (q : ℝ) ^ (-nu) := hpow
    _ ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := happrox p q hq
