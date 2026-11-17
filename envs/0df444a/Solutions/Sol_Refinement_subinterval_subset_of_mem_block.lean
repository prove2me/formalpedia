-- Prove2me | solution 1 for Refinement.subinterval_subset_of_mem_block
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:16:54.616535+00:00
-- url     : https://prove2.me/submissions/7617ad43-2c83-473b-b18b-9ee11c9824ec

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise
noncomputable section

private theorem source_subinterval_subset_of_mem_block
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    {i : Fin P.n} {j : Fin P'.n}
    (hj : j ∈ R.block i) :
    Partition.subinterval P' j ⊆ Partition.subinterval P i := by
  classical

  unfold Refinement.block at hj
  dsimp only at hj

  rcases Finset.mem_image.mp hj with ⟨t, _htmem, htj⟩

  -- `t` is an element of the attached range, so `t.1` lies in the range.
  have ht_lt :
      t.1 <
        (R.index i.succ).val - (R.index i.castSucc).val := by
    exact Finset.mem_range.mp t.2

  -- The image equality says that the value of `j` is `lo + t`.
  have hjval :
      j.val = (R.index i.castSucc).val + t.1 := by
    exact (congrArg Fin.val htj).symm

  -- Left endpoint inequality:
  -- `R.index i ≤ j`.
  have hleft :
      R.index i.castSucc ≤ j.castSucc := by
    change (R.index i.castSucc).val ≤ j.val
    rw [hjval]
    omega

  -- Right endpoint inequality:
  -- `j + 1 ≤ R.index (i+1)`.
  have hright :
      j.succ ≤ R.index i.succ := by
    change j.val + 1 ≤ (R.index i.succ).val
    rw [hjval]
    omega

  intro x hx
  constructor
  · -- old left endpoint ≤ x
    have hpts_left :
        P'.pts (R.index i.castSucc) ≤ P'.pts j.castSucc :=
      P'.strict_mono.monotone hleft

    calc
      P.pts i.castSucc = P'.pts (R.index i.castSucc) :=
        R.index_spec i.castSucc
      _ ≤ P'.pts j.castSucc :=
        hpts_left
      _ ≤ x :=
        hx.1

  · -- x ≤ old right endpoint
    have hpts_right :
        P'.pts j.succ ≤ P'.pts (R.index i.succ) :=
      P'.strict_mono.monotone hright

    calc
      x ≤ P'.pts j.succ :=
        hx.2
      _ ≤ P'.pts (R.index i.succ) :=
        hpts_right
      _ = P.pts i.succ :=
        (R.index_spec i.succ).symm

theorem solution
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    {i : Fin P.n} {j : Fin P'.n}
    (hj : j ∈ R.block i) :
    Partition.subinterval P' j ⊆ Partition.subinterval P i := by
  exact source_subinterval_subset_of_mem_block R hj
