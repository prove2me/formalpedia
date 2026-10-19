-- Prove2me | solution 1 for PermanentRollout.sum_powerset_factorial_mul_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/d7f5fda7-068f-4c4e-9dcb-31a8891bc47a

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {α : Type*}
    [DecidableEq α] (rows : Finset α) :
    (∑ selected ∈ rows.powerset,
      selected.card.factorial * (rows \ selected).card.factorial) =
        (rows.card + 1).factorial := by
  classical
  rw [Finset.sum_powerset]
  calc
    (∑ k ∈ Finset.range (rows.card + 1),
        ∑ selected ∈ rows.powersetCard k,
          selected.card.factorial * (rows \ selected).card.factorial) =
      ∑ _k ∈ Finset.range (rows.card + 1), rows.card.factorial := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkle : k ≤ rows.card := by
          have := Finset.mem_range.mp hk
          omega
        calc
          (∑ selected ∈ rows.powersetCard k,
              selected.card.factorial *
                (rows \ selected).card.factorial) =
            ∑ _selected ∈ rows.powersetCard k,
              k.factorial * (rows.card - k).factorial := by
                apply Finset.sum_congr rfl
                intro selected hselected
                obtain ⟨hsubset, hcard⟩ :=
                  Finset.mem_powersetCard.mp hselected
                rw [Finset.card_sdiff_of_subset hsubset, hcard]
          _ = rows.card.choose k *
              (k.factorial * (rows.card - k).factorial) := by
                simp [Finset.card_powersetCard]
          _ = rows.card.factorial := by
                simpa [mul_assoc] using
                  (Nat.choose_mul_factorial_mul_factorial hkle)
    _ = (rows.card + 1).factorial := by
      simp [Nat.factorial_succ, mul_comm]
end PermanentRollout
