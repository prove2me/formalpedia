-- Prove2me | solution 3 for PiIrrationality.openai_bound_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T11:15:31.157634+00:00
-- url     : https://prove2.me/submissions/c0c01089-edbf-4140-93a1-a5b771b58cbe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PiIrrationality_UpperBound
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Theorems.Thm_OAI_PiExponent_pi_eventual_lower_bound
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution : PiIrrationality.UpperBound (2 : ℝ) := by
  change ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ,
    ∀ (p : ℤ) (q : ℕ), 0 < q → Q ≤ q →
      1 / (q : ℝ) ^ ((2 : ℝ) + ε) < |Real.pi - (p : ℝ) / (q : ℝ)|
  intro ε hε
  have hnu : (2 : ℝ) < 2 + ε / 2 := by linarith
  obtain ⟨Q, hQ, hbound⟩ := OAI.PiExponent.pi_eventual_lower_bound (2 + ε / 2) hnu
  refine ⟨Q, ?_⟩
  intro p q _ hq
  have hq2 : 2 ≤ q := le_trans hQ hq
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have he : -((2 : ℝ) + ε) < -(2 + ε / 2) := by linarith
  have hpow := Real.rpow_lt_rpow_of_exponent_lt hq1 he
  have hidentity : 1 / (q : ℝ) ^ ((2 : ℝ) + ε) =
      (q : ℝ) ^ (-((2 : ℝ) + ε)) := by
    rw [Real.rpow_neg (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) hq1))]
    simp only [one_div]
  rw [hidentity]
  exact lt_of_lt_of_le hpow (hbound p q hq)
