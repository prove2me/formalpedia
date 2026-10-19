-- Prove2me | solution 1 for PermanentRollout.partition_cycle_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/fc272ca6-83a8-4ec4-a880-41e9e1f8e9e3

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_partition_cycle_factorial_empty
import Theorems.Thm_PermanentRollout_partition_cycle_factorial_fiber
import Theorems.Thm_PermanentRollout_sum_powerset_factorial_mul_factorial

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {t : ℕ} (rows : Finset (Fin t)) :
    (∑ partition : Finpartition rows,
      ∏ block ∈ partition.parts, (block.card - 1).factorial) =
        rows.card.factorial := by
  classical
  induction rows using Finset.strongInduction with
  | H rows ih =>
    by_cases hempty : rows = ∅
    · subst rows
      exact partition_cycle_factorial_empty t
    · obtain ⟨distinguished, hdistinguished⟩ :=
        Finset.nonempty_iff_ne_empty.mpr hempty
      have hmaps :
          ∀ partition ∈ (Finset.univ : Finset (Finpartition rows)),
            (partition.part distinguished).erase distinguished ∈
              (rows.erase distinguished).powerset := by
        intro partition _
        apply Finset.mem_powerset.mpr
        intro row hrow
        obtain ⟨hne, hpart⟩ := Finset.mem_erase.mp hrow
        exact Finset.mem_erase.mpr
          ⟨hne, partition.part_subset distinguished hpart⟩
      calc
        (∑ partition : Finpartition rows,
            ∏ block ∈ partition.parts, (block.card - 1).factorial) =
          ∑ selected ∈ (rows.erase distinguished).powerset,
            ∑ partition ∈
                (Finset.univ : Finset (Finpartition rows)).filter
                  (fun partition =>
                    (partition.part distinguished).erase distinguished =
                      selected),
              ∏ block ∈ partition.parts, (block.card - 1).factorial :=
            (Finset.sum_fiberwise_of_maps_to hmaps
              (fun partition : Finpartition rows =>
                ∏ block ∈ partition.parts, (block.card - 1).factorial)).symm
        _ = ∑ selected ∈ (rows.erase distinguished).powerset,
              selected.card.factorial *
                (rows \ insert distinguished selected).card.factorial := by
          apply Finset.sum_congr rfl
          intro selected hselected
          have hsubselected : selected ⊆ rows.erase distinguished :=
            Finset.mem_powerset.mp hselected
          rw [partition_cycle_factorial_fiber rows distinguished
            hdistinguished selected hsubselected]
          have hblock : insert distinguished selected ⊆ rows := by
            intro row hrow
            rcases Finset.mem_insert.mp hrow with hrow | hrow
            · simpa [hrow] using hdistinguished
            · exact (Finset.mem_erase.mp (hsubselected hrow)).2
          have hnonempty : (insert distinguished selected).Nonempty :=
            ⟨distinguished,
              Finset.mem_insert_self distinguished selected⟩
          rw [ih (rows \ insert distinguished selected)
            (Finset.sdiff_ssubset hblock hnonempty)]
        _ = ∑ selected ∈ (rows.erase distinguished).powerset,
              selected.card.factorial *
                ((rows.erase distinguished) \ selected).card.factorial := by
          apply Finset.sum_congr rfl
          intro selected _
          have hcomplement :
              rows \ insert distinguished selected =
                (rows.erase distinguished) \ selected := by
            ext row
            simp [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert,
              and_assoc, and_left_comm]
          rw [hcomplement]
        _ = ((rows.erase distinguished).card + 1).factorial :=
          sum_powerset_factorial_mul_factorial (rows.erase distinguished)
        _ = rows.card.factorial := by
          rw [Finset.card_erase_of_mem hdistinguished]
          congr 1
          have hpos : 0 < rows.card := Finset.card_pos.mpr
            ⟨distinguished, hdistinguished⟩
          omega
end PermanentRollout
