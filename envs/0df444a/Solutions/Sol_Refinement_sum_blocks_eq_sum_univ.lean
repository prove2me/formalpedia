-- Prove2me | solution 1 for Refinement.sum_blocks_eq_sum_univ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:19:30.297043+00:00
-- url     : https://prove2.me/submissions/dd21e238-3c8d-4cdd-8edf-0199a3e7e058

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F012
import Mathlib.Tactic
import Theorems.Thm_Refinement_block_disjoint
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise Interval
noncomputable section

private theorem source_sum_blocks_eq_sum_univ
    {a b : ℝ}
    {P P' : Partition a b}
    (R : Refinement P P')
    (g : Fin P'.n → ℝ) :
    (∑ i : Fin P.n, ∑ j ∈ R.block i, g j)
      =
    ∑ j : Fin P'.n, g j := by
  classical

  change
    Finset.sum (Finset.univ : Finset (Fin P.n))
      (fun i => Finset.sum (R.block i) g)
      =
    Finset.sum (Finset.univ : Finset (Fin P'.n)) g

  have hsum :
      Finset.sum
        ((Finset.univ : Finset (Fin P.n)).biUnion
          (fun i => R.block i))
        g
        =
      Finset.sum (Finset.univ : Finset (Fin P.n))
        (fun i => Finset.sum (R.block i) g) := by
    apply Finset.sum_biUnion
    intro i _hi k _hk hik
    exact Refinement.block_disjoint R hik

  calc
    Finset.sum (Finset.univ : Finset (Fin P.n))
      (fun i => Finset.sum (R.block i) g)
        =
      Finset.sum
        ((Finset.univ : Finset (Fin P.n)).biUnion
          (fun i => R.block i))
        g := hsum.symm
    _ =
      Finset.sum (Finset.univ : Finset (Fin P'.n)) g := by
        rw [Refinement.biUnion_block_eq_univ R]

theorem solution
    {a b : ℝ}
    {P P' : Partition a b}
    (R : Refinement P P')
    (g : Fin P'.n → ℝ) :
    (∑ i : Fin P.n, ∑ j ∈ R.block i, g j)
      =
    ∑ j : Fin P'.n, g j := by
  exact source_sum_blocks_eq_sum_univ R g
