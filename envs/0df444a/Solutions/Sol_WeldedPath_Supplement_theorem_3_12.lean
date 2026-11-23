-- Prove2me | solution 1 for WeldedPath.Supplement.theorem_3_12
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:40:39.42683+00:00
-- url     : https://prove2.me/submissions/538f05ef-f95a-4edb-a731-fd79aacbe982
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_Supplement_pWtSplit
import Theorems.Thm_WeldedPath_Supplement_short_output_crossing_bound
import Theorems.Thm_WeldedPath_Supplement_long_output_label_bound

open WeldedPath WeldedPath.Supplement QAlgorithms

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
        (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
          List (Fin 3 × Qubits (2 * n + 1))),
      80 * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      pWt l G A out ≤ C * (pCross l G A + (q : ℝ) / (2 : ℝ) ^ (n - l)) := by
  obtain ⟨Cs, hCs, hs⟩ := short_output_crossing_bound
  obtain ⟨Cl, hCl, hl⟩ := long_output_label_bound
  refine ⟨Cs + Cl, by positivity, ?_⟩
  intro n l heven hl2 hln G hG W instF instD q hq A out hNl
  have hs' := hs n l heven hl2 hln G hG W q hq A out hNl
  have hl' := hl n l heven hl2 hln G hG W q hq A out hNl
  rw [pWt_eq_add]
  have hpc : 0 ≤ pCross l G A := by
    unfold pCross
    positivity
  nlinarith
