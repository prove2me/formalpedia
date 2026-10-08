-- Prove2me | solution 1 for PiIrrationality.openai_bound_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T06:20:49.802341+00:00
-- url     : https://prove2.me/submissions/7e2032bf-c97d-4115-9caf-a734e883dd72
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PiIrrationality_UpperBound
import Theorems.Thm_OAI_PiExponent_main

theorem solution : PiIrrationality.UpperBound (2 : ℝ) := by
  intro ε hε
  obtain ⟨Q, hQ, hbound⟩ := OAI.PiExponent.main.1 (2 + ε / 2) (by linarith)
  refine ⟨Q.toNat, ?_⟩
  intro p q hq hQq
  have hQq' : Q ≤ (q : ℤ) := by omega
  have hq2 : 2 ≤ q := by omega
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  calc
    1 / (q : ℝ) ^ (2 + ε) = (q : ℝ) ^ (-(2 + ε)) := by
      rw [Real.rpow_neg (by positivity), one_div]
    _ < (q : ℝ) ^ (-(2 + ε / 2)) :=
      Real.rpow_lt_rpow_of_exponent_lt hq1 (by linarith)
    _ ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by
      simpa only [Int.cast_natCast] using hbound p (q : ℤ) hQq'

