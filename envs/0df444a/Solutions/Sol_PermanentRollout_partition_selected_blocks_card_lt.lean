-- Prove2me | solution 1 for PermanentRollout.partition_selected_blocks_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/9b3e40e3-1715-49a6-975d-9b1187572505

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {t : ℕ}
    {rows : Finset (Fin t)} (partition : Finpartition rows)
    (selected : Finset (Finset (Fin t)))
    (hselected : selected ⊆ partition.parts)
    (hne : selected ≠ partition.parts) :
    (∑ block ∈ selected, block.card) < rows.card := by
  classical
  have hproper : ¬partition.parts ⊆ selected := by
    intro hreverse
    exact hne (Finset.Subset.antisymm hselected hreverse)
  obtain ⟨block, hblock, hnot⟩ := Finset.not_subset.mp hproper
  rw [← partition.sum_card_parts]
  exact Finset.sum_lt_sum_of_subset hselected hblock hnot
    (Finset.card_pos.mpr (partition.nonempty_of_mem_parts hblock))
    (fun _ _ _ => Nat.zero_le _)
end PermanentRollout
