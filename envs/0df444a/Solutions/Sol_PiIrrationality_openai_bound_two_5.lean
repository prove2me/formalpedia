-- Prove2me | solution 5 for PiIrrationality.openai_bound_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:03:51.95749+00:00
-- url     : https://prove2.me/submissions/bd3812c0-e439-4be5-8603-f8a0827345de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Definitions.Def_PiIrrationality_UpperBound
import Theorems.Thm_OAI_PiExponent_rational_approximation_lower_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution : PiIrrationality.UpperBound (2 : ℝ) := by
  intro ε hε
  have hν : (2 : ℝ) < 2 + ε / 2 := by linarith
  obtain ⟨Q, hQ, hbound⟩ :=
    OAI.PiExponent.rational_approximation_lower_bound (2 + ε / 2) hν
  refine ⟨Q, ?_⟩
  intro p q hqpos hq
  have hq2 : 2 ≤ q := le_trans hQ hq
  have hqgt : (1 : ℝ) < (q : ℝ) := by
    exact_mod_cast (show 1 < q by omega)
  have hlt : (q : ℝ) ^ (-(2 + ε)) <
      (q : ℝ) ^ (-(2 + ε / 2)) := by
    apply Real.rpow_lt_rpow_of_exponent_lt hqgt
    linarith
  calc
    1 / (q : ℝ) ^ (2 + ε) =
        (q : ℝ) ^ (-(2 + ε)) := by
          rw [one_div]
          exact (Real.rpow_neg (by positivity : (0 : ℝ) ≤ (q : ℝ)) (2 + ε)).symm
    _ < (q : ℝ) ^ (-(2 + ε / 2)) := hlt
    _ ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := hbound p q hq
