-- Prove2me | solution 1 for Refinement.mem_block_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:14:51.106054+00:00
-- url     : https://prove2.me/submissions/33a880ba-15c1-4f46-a040-a31db28b0f9f

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise
noncomputable section

private theorem source_refinement_mem_block_iff
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    {i : Fin P.n} {j : Fin P'.n} :
    j ∈ R.block i ↔
      (R.index i.castSucc).val ≤ j.val ∧
      j.val < (R.index i.succ).val := by
  classical
  unfold Refinement.block
  dsimp
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨t, _htmem, htj⟩

    have htlt :
        t.1 < (R.index i.succ).val - (R.index i.castSucc).val := by
      exact Finset.mem_range.mp t.2

    have hjval :
        j.val = (R.index i.castSucc).val + t.1 := by
      exact (congrArg Fin.val htj).symm

    constructor
    · rw [hjval]
      omega
    · rw [hjval]
      omega

  · intro hj
    rcases hj with ⟨hlo, hhi⟩

    let tnat : ℕ := j.val - (R.index i.castSucc).val

    have htlt :
        tnat < (R.index i.succ).val - (R.index i.castSucc).val := by
      dsimp [tnat]
      omega

    let t :
        {x // x ∈ Finset.range
          ((R.index i.succ).val - (R.index i.castSucc).val)} :=
      ⟨tnat, Finset.mem_range.mpr htlt⟩

    apply Finset.mem_image.mpr
    refine ⟨t, ?_, ?_⟩
    · exact Finset.mem_attach _ _
    · apply Fin.ext
      dsimp [t, tnat]
      omega

theorem solution
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    {i : Fin P.n} {j : Fin P'.n} :
    j ∈ R.block i ↔
      (R.index i.castSucc).val ≤ j.val ∧
      j.val < (R.index i.succ).val := by
  exact source_refinement_mem_block_iff R
