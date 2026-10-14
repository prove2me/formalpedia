-- Prove2me | solution 2 for PiIrrationality.openai_bound_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:28:34.038986+00:00
-- url     : https://prove2.me/submissions/5bf1a83d-0e23-4eb0-8ca6-20a93bc1746e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Theorems.Thm_OAI_PiExponent_pi_eventual_lower_bound
import Definitions.Def_PiIrrationality_UpperBound

-- Local integration target. The source import will be platformized only after
-- the complete source closure and its axioms have passed verification.
theorem solution : PiIrrationality.UpperBound (2 : ℝ) := by
  intro ε hε
  obtain ⟨Q, hQ, hLower⟩ :=
    OAI.PiExponent.pi_eventual_lower_bound (2 + ε / 2) (by linarith)
  refine ⟨Q, ?_⟩
  intro p q _hqpos hq
  have hqTwo : 2 ≤ q := hQ.trans hq
  have hqOne : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  rw [one_div, ← Real.rpow_neg (Nat.cast_nonneg q)]
  exact (Real.rpow_lt_rpow_of_exponent_lt hqOne
    (by linarith : -(2 + ε) < -(2 + ε / 2))).trans_le (hLower p q hq)

