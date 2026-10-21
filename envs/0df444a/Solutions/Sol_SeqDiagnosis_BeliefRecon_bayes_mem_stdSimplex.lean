-- Prove2me | solution 1 for SeqDiagnosis.BeliefRecon.bayes_mem_stdSimplex
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T09:57:30.126965+00:00
-- url     : https://prove2.me/submissions/5af44e56-1e69-4e63-a75c-3cbf356afc0d

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Bayes

open SeqDiagnosis.BeliefRecon

theorem solution {Y : Type*} {N : ℕ}
    (f : Fin (N + 1) → Y → ℝ) (y : Y) (hf : ∀ i, 0 < f i y)
    (q : Fin (N + 1) → ℝ) (hq : q ∈ stdSimplex ℝ (Fin (N + 1))) :
    0 < ∑ i, q i * f i y ∧ bayes f q y ∈ stdSimplex ℝ (Fin (N + 1)) := by
  obtain ⟨hq0, hq1⟩ := hq
  have hpos : 0 < ∑ i, q i * f i y := by
    obtain ⟨k, hk⟩ : ∃ k, 0 < q k := by
      by_contra h
      push Not at h
      have : ∑ i, q i ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
      linarith
    calc (0:ℝ) < q k * f k y := mul_pos hk (hf k)
      _ ≤ ∑ i, q i * f i y :=
        Finset.single_le_sum (f := fun i => q i * f i y)
          (fun i _ => mul_nonneg (hq0 i) (hf i).le) (Finset.mem_univ k)
  refine ⟨hpos, ?_, ?_⟩
  · intro j
    exact div_nonneg (mul_nonneg (hq0 j) (hf j).le) hpos.le
  · simp only [bayes]
    rw [← Finset.sum_div]
    exact div_self hpos.ne'
