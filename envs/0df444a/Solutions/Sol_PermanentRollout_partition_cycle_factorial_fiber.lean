-- Prove2me | solution 1 for PermanentRollout.partition_cycle_factorial_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/90dd4a1a-d208-4dfd-9c6e-c7ffd83c459c

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {α : Type*} [DecidableEq α] (rows : Finset α)
    (distinguished : α) (hdistinguished : distinguished ∈ rows)
    (selected : Finset α) (hselected : selected ⊆ rows.erase distinguished) :
    (∑ partition ∈
        (Finset.univ : Finset (Finpartition rows)).filter
          (fun partition => (partition.part distinguished).erase distinguished =
            selected),
        ∏ block ∈ partition.parts, (block.card - 1).factorial) =
      selected.card.factorial *
        ∑ partition : Finpartition (rows \ insert distinguished selected),
          ∏ block ∈ partition.parts, (block.card - 1).factorial := by
  classical
  have hnot : distinguished ∉ selected := by
    intro hmem
    exact Finset.notMem_erase distinguished rows (hselected hmem)
  simpa [hnot] using
    (partition_weight_fiber
      (fun block : Finset α => (block.card - 1).factorial)
      rows distinguished hdistinguished selected hselected)
end PermanentRollout
