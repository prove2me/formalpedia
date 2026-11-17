-- Prove2me | solution 1 for Refinement.exists_mem_block
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:17:54.361196+00:00
-- url     : https://prove2.me/submissions/beee2025-3e55-4784-9cde-567752c05f97

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F011
import Mathlib.Tactic
import Theorems.Thm_Refinement_mem_block_iff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise Interval
noncomputable section

private theorem source_exists_mem_block
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    (j : Fin P'.n) :
    ∃ i : Fin P.n, j ∈ R.block i := by
  classical

  let Q : ℕ → Prop :=
    fun q =>
      ∃ hq : q < P.n + 1,
        j.val < (R.index ⟨q, hq⟩).val

  have hQ : ∃ q : ℕ, Q q := by
    refine ⟨P.n, ?_⟩
    dsimp [Q]
    refine ⟨by omega, ?_⟩

    have hlast_fin :
        (⟨P.n, by omega⟩ : Fin (P.n + 1)) = Fin.last P.n := by
      apply Fin.ext
      simp

    have hlast_val :
        (R.index (⟨P.n, by omega⟩ : Fin (P.n + 1))).val = P'.n := by
      rw [hlast_fin, Refinement.index_last R]
      rfl

    rw [hlast_val]
    exact j.isLt

  let q : ℕ := Nat.find hQ

  have hqspec : Q q := Nat.find_spec hQ

  rcases hqspec with ⟨hq_bound, hj_lt_q⟩

  have hq_pos : 0 < q := by
    by_contra hnot
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hnot

    have hfin0 :
        (⟨q, hq_bound⟩ : Fin (P.n + 1)) =
          (0 : Fin (P.n + 1)) := by
      apply Fin.ext
      simp [hq0]

    have : j.val < 0 := by
      calc
        j.val < (R.index (⟨q, hq_bound⟩ : Fin (P.n + 1))).val := hj_lt_q
        _ = (R.index (0 : Fin (P.n + 1))).val := by
          rw [hfin0]
        _ = 0 := by
          rw [Refinement.index_zero R]
          rfl

    omega

  have hprev_lt_q : q - 1 < q := by
    omega

  have hnot_prev : ¬ Q (q - 1) := by
    exact Nat.find_min hQ hprev_lt_q

  have hprev_bound : q - 1 < P.n + 1 := by
    omega

  have hprev_le :
      (R.index (⟨q - 1, hprev_bound⟩ : Fin (P.n + 1))).val ≤ j.val := by
    by_contra hnot_le
    have hlt :
        j.val <
          (R.index (⟨q - 1, hprev_bound⟩ : Fin (P.n + 1))).val :=
      Nat.lt_of_not_ge hnot_le

    exact hnot_prev ⟨hprev_bound, hlt⟩

  let i : Fin P.n := ⟨q - 1, by omega⟩

  refine ⟨i, ?_⟩

  apply (Refinement.mem_block_iff R (i := i) (j := j)).mpr
  constructor
  · have hcast :
        i.castSucc =
          (⟨q - 1, hprev_bound⟩ : Fin (P.n + 1)) := by
      apply Fin.ext
      simp [i]

    simpa [hcast] using hprev_le

  · have hsucc :
        i.succ =
          (⟨q, hq_bound⟩ : Fin (P.n + 1)) := by
      apply Fin.ext
      simp [i]
      omega

    simpa [hsucc] using hj_lt_q

theorem solution
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    (j : Fin P'.n) :
    ∃ i : Fin P.n, j ∈ R.block i := by
  exact source_exists_mem_block R j
