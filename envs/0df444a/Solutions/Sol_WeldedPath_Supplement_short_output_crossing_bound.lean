-- Prove2me | solution 1 for WeldedPath.Supplement.short_output_crossing_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:35:38.682862+00:00
-- url     : https://prove2.me/submissions/6602b6bc-78c4-4921-ba49-d28e32574ffb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_Supplement_pWtSplit
import Theorems.Thm_WeldedPath_Supplement_short_output_sqrt_comparison

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
      pWtLe l G A out ≤ C * (pCross l G A + (q : ℝ) / (2 : ℝ) ^ (n - l)) := by
  obtain ⟨C, hC, hcomp⟩ := short_output_sqrt_comparison
  refine ⟨2 * (C ^ 2 + 1), by positivity, ?_⟩
  intro n l hn hl hln G hG W instF instD q hq A out hN
  have h := hcomp n l hn hl hln G hG W q hq A out hN
  have hp : 0 ≤ pWtLe l G A out := by
    classical
    unfold pWtLe WeldedInstance.probOver avgOver QAlgorithms.probEvent QAlgorithms.prob
    positivity
  have hc : 0 ≤ pCross l G A := by
    unfold pCross
    positivity
  have hr : 0 ≤ (q : ℝ) / (2 : ℝ) ^ (n - l) := by positivity
  have hs : pWtLe l G A out ≤
      (Real.sqrt (pCross l G A) + C * Real.sqrt ((q : ℝ) / (2 : ℝ) ^ (n - l))) ^ 2 := by
    calc
      pWtLe l G A out = Real.sqrt (pWtLe l G A out) ^ 2 := (Real.sq_sqrt hp).symm
      _ ≤ (Real.sqrt (pCross l G A) +
          C * Real.sqrt ((q : ℝ) / (2 : ℝ) ^ (n - l))) ^ 2 := by gcongr
  calc
    pWtLe l G A out ≤
        (Real.sqrt (pCross l G A) + C * Real.sqrt ((q : ℝ) / (2 : ℝ) ^ (n - l))) ^ 2 := hs
    _ ≤ 2 * (pCross l G A + C ^ 2 * ((q : ℝ) / (2 : ℝ) ^ (n - l))) := by
      have hsq : (C * Real.sqrt ((q : ℝ) / (2 : ℝ) ^ (n - l))) ^ 2 =
          C ^ 2 * ((q : ℝ) / (2 : ℝ) ^ (n - l)) := by
        rw [mul_pow, Real.sq_sqrt hr]
      have hcsq : Real.sqrt (pCross l G A) ^ 2 = pCross l G A := Real.sq_sqrt hc
      nlinarith [sq_nonneg (Real.sqrt (pCross l G A) -
        C * Real.sqrt ((q : ℝ) / (2 : ℝ) ^ (n - l)))]
    _ ≤ 2 * (C ^ 2 + 1) * (pCross l G A + (q : ℝ) / (2 : ℝ) ^ (n - l)) := by
      nlinarith [mul_nonneg (sq_nonneg C) hc]
