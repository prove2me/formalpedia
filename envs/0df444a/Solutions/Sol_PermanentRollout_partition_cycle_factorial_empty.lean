-- Prove2me | solution 1 for PermanentRollout.partition_cycle_factorial_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/93989d18-9816-477a-ab66-d1afb1248bfe

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution (t : ℕ) :
    (∑ partition : Finpartition (∅ : Finset (Fin t)),
      ∏ block ∈ partition.parts, (block.card - 1).factorial) =
        (0 : ℕ).factorial := by
  classical
  let emptyPartition : Finpartition (∅ : Finset (Fin t)) :=
    Finpartition.empty (Finset (Fin t))
  have huniv :
      (Finset.univ : Finset (Finpartition (∅ : Finset (Fin t)))) =
        {emptyPartition} := by
    ext partition
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    change partition = Finpartition.empty (Finset (Fin t))
    exact partition_empty_eq partition
  rw [huniv]
  simp [emptyPartition, Finpartition.empty]
end PermanentRollout
