-- Prove2me | solution 1 for StaticQuote.Clairvoyant.superadditive
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:55:09.990574+00:00
-- url     : https://prove2.me/submissions/96ad8acf-aa8e-47ed-934e-ebe3008accf7

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting

open MeasureTheory Filter
open scoped ENNReal
open StaticQuote.Clairvoyant

theorem solution {Ω : Type*} [MeasurableSpace Ω] (Q : Model Ω) (ω : Ω) (N : ℕ) :
    Q.gamma 1 N ω + Q.gamma (N + 1) (2 * N) ω ≤ Q.gamma 1 (2 * N) ω := by
  unfold Model.gamma
  refine le_iInf₂ fun y hy => ?_
  have h1 : Q.IsSchedule 1 N y ω := by
    refine ⟨fun n hn => hy.1 n ?_, fun n hn => hy.2 n ?_⟩
    · simp only [Finset.mem_Icc] at hn ⊢; omega
    · simp only [Finset.mem_Ico] at hn ⊢; omega
  have h2 : Q.IsSchedule (N + 1) (2 * N) y ω := by
    refine ⟨fun n hn => hy.1 n ?_, fun n hn => hy.2 n ?_⟩
    · simp only [Finset.mem_Icc] at hn ⊢; omega
    · simp only [Finset.mem_Ico] at hn ⊢; omega
  have hsplit : ∀ f : ℕ → ℝ≥0∞, ∑ n ∈ Finset.Icc 1 (2 * N), f n =
      ∑ n ∈ Finset.Icc 1 N, f n + ∑ n ∈ Finset.Icc (N + 1) (2 * N), f n := by
    intro f
    rw [← Finset.sum_union]
    · congr 1
      ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    · rw [Finset.disjoint_left]; intro n h h'; simp only [Finset.mem_Icc] at h h'; omega
  rw [hsplit]
  exact add_le_add (iInf₂_le y h1) (iInf₂_le y h2)
