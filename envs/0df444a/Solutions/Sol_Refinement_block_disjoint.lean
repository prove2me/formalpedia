-- Prove2me | solution 1 for Refinement.block_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:16:46.911211+00:00
-- url     : https://prove2.me/submissions/3adaedc6-bf23-49e6-83e9-7c883c839748

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
import Mathlib.Tactic
import Theorems.Thm_Refinement_mem_block_iff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise
noncomputable section

private theorem source_block_disjoint
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    {i k : Fin P.n} (hik : i ≠ k) :
    Disjoint (R.block i) (R.block k) := by
  classical

  refine Finset.disjoint_left.mpr ?_
  intro j hji hjk

  have hji' :
      (R.index i.castSucc).val ≤ j.val ∧
      j.val < (R.index i.succ).val :=
    (Refinement.mem_block_iff R (i := i) (j := j)).mp hji

  have hjk' :
      (R.index k.castSucc).val ≤ j.val ∧
      j.val < (R.index k.succ).val :=
    (Refinement.mem_block_iff R (i := k) (j := j)).mp hjk

  rcases lt_or_gt_of_ne hik with hiklt | hkilt

  · -- case `i < k`
    have hbase : i.succ ≤ k.castSucc := by
      change i.val + 1 ≤ k.val
      exact Nat.succ_le_of_lt hiklt

    have hidx :
        R.index i.succ ≤ R.index k.castSucc :=
      R.strictMono_index.monotone hbase

    have hidx_val :
        (R.index i.succ).val ≤ (R.index k.castSucc).val := by
      exact hidx

    omega

  · -- case `k < i`
    have hbase : k.succ ≤ i.castSucc := by
      change k.val + 1 ≤ i.val
      exact Nat.succ_le_of_lt hkilt

    have hidx :
        R.index k.succ ≤ R.index i.castSucc :=
      R.strictMono_index.monotone hbase

    have hidx_val :
        (R.index k.succ).val ≤ (R.index i.castSucc).val := by
      exact hidx

    omega

theorem solution
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    {i k : Fin P.n} (hik : i ≠ k) :
    Disjoint (R.block i) (R.block k) := by
  exact source_block_disjoint R hik
