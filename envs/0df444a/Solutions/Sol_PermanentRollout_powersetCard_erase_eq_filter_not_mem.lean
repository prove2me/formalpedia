-- Prove2me | solution 1 for PermanentRollout.powersetCard_erase_eq_filter_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/0b0d6a01-f4db-4ffa-b350-bf3913362925

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {α : Type*} [DecidableEq α]
    (s : Finset α) (i : α) (q : ℕ) :
    (s.erase i).powersetCard q =
      (s.powersetCard q).filter (fun rows => i ∉ rows) := by
  ext rows
  simp only [Finset.mem_powersetCard, Finset.mem_filter]
  constructor
  · rintro ⟨hrows, hcard⟩
    refine ⟨⟨fun j hj => (Finset.mem_erase.mp (hrows hj)).2, hcard⟩, ?_⟩
    intro hi
    exact Finset.notMem_erase i s (hrows hi)
  · rintro ⟨⟨hrows, hcard⟩, hi⟩
    refine ⟨fun j hj => Finset.mem_erase.mpr ⟨?_, hrows hj⟩, hcard⟩
    intro heq
    exact hi (heq ▸ hj)
end PermanentRollout
