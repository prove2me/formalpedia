-- Prove2me | solution 2 for SeqDiagnosis.BeliefRecon.bayes_mem_stdSimplex
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:52:02.878464+00:00
-- url     : https://prove2.me/submissions/edf235cb-10dd-4383-8906-cbefca43a9a4

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Bayes

set_option autoImplicit false
open SeqDiagnosis.BeliefRecon

theorem solution {Y : Type*} {N : ℕ}
    (f : Fin (N + 1) → Y → ℝ) (y : Y) (hf : ∀ i, 0 < f i y)
    (q : Fin (N + 1) → ℝ) (hq : q ∈ stdSimplex ℝ (Fin (N + 1))) :
    0 < ∑ i, q i * f i y ∧ bayes f q y ∈ stdSimplex ℝ (Fin (N + 1)) := by
  obtain ⟨hq0, hq1⟩ := hq
  have hD : 0 < ∑ i, q i * f i y := by
    obtain ⟨k, hk⟩ : ∃ k, 0 < q k := by
      by_contra h
      push_neg at h
      have : ∑ i, q i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (hq0 i)
      rw [this] at hq1; exact zero_ne_one hq1
    exact Finset.sum_pos' (fun i _ => mul_nonneg (hq0 i) (hf i).le)
      ⟨k, Finset.mem_univ _, mul_pos hk (hf k)⟩
  refine ⟨hD, fun j => ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (hq0 j) (hf j).le) hD.le
  · simp only [bayes]
    rw [← Finset.sum_div, div_self hD.ne']
