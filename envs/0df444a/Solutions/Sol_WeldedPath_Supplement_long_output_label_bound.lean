-- Prove2me | solution 1 for WeldedPath.Supplement.long_output_label_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:31:09.154827+00:00
-- url     : https://prove2.me/submissions/94b06cdc-39df-4279-936f-4cdddd0156b6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_Supplement_pWtSplit
import Theorems.Thm_WeldedPath_Supplement_long_output_label_comparison
import Theorems.Thm_WeldedPath_Supplement_long_output_recorded_vanishes

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
      pWtGt l G A out ≤ C * ((q : ℝ) / (2 : ℝ) ^ (n - l)) := by
  obtain ⟨C, hC, hcomp⟩ := long_output_label_comparison
  refine ⟨C ^ 2 + 1, by positivity, ?_⟩
  intro n l hn hl hln G hG W instF instD q hq A out hN
  have h := hcomp n l hn hl hln G hG W q hq A out hN
  have hzero := long_output_recorded_vanishes n l hn hl hln G hG W q hq A out
  rw [hzero, Real.sqrt_zero, zero_add] at h
  have hp : 0 ≤ pWtGt l G A out := by
    classical
    unfold pWtGt WeldedInstance.probOver avgOver QAlgorithms.probEvent QAlgorithms.prob
    positivity
  have hrN : 0 ≤ (q : ℝ) / (2 : ℝ) ^ n := by positivity
  have hrL : 0 ≤ (q : ℝ) / (2 : ℝ) ^ (n - l) := by positivity
  have hs : pWtGt l G A out ≤ C ^ 2 * ((q : ℝ) / (2 : ℝ) ^ n) := by
    calc
      pWtGt l G A out = Real.sqrt (pWtGt l G A out) ^ 2 := (Real.sq_sqrt hp).symm
      _ ≤ (C * Real.sqrt ((q : ℝ) / (2 : ℝ) ^ n)) ^ 2 := by gcongr
      _ = C ^ 2 * ((q : ℝ) / (2 : ℝ) ^ n) := by
        rw [mul_pow, Real.sq_sqrt hrN]
  have hden : (2 : ℝ) ^ (n - l) ≤ (2 : ℝ) ^ n := by
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le n l)
  have hr : (q : ℝ) / (2 : ℝ) ^ n ≤ (q : ℝ) / (2 : ℝ) ^ (n - l) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  calc
    pWtGt l G A out ≤ C ^ 2 * ((q : ℝ) / (2 : ℝ) ^ n) := hs
    _ ≤ C ^ 2 * ((q : ℝ) / (2 : ℝ) ^ (n - l)) :=
      mul_le_mul_of_nonneg_left hr (sq_nonneg C)
    _ ≤ (C ^ 2 + 1) * ((q : ℝ) / (2 : ℝ) ^ (n - l)) := by nlinarith
