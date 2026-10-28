-- Prove2me | solution 1 for PigeonholeDesign.Upper.lemma_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:56:52.087985+00:00
-- url     : https://prove2.me/submissions/1d29352c-ce88-4203-9eea-c598156feacb

import Mathlib
import Theorems.Thm_PigeonholeDesign_MultiDim_lemma_EC_1


theorem solution (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - 2 / (n : ℝ) ^ 2 ≤
      ∑ k ∈ (Finset.range (n + 1)).filter
          (fun k : ℕ => |(k : ℝ) - p * n| ≤ Real.sqrt (n * Real.log n)),
        (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
  apply PigeonholeDesign.MultiDim.lemma_EC_1 <;> assumption


