-- Prove2me | solution 1 for PermanentRollout.incidenceRowBlock_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/c9f02cb2-d07d-4ce5-8e71-4dfaccc226a4

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution (t : ℕ) :
    Fintype.card (IncidenceRowBlock t) = 2 ^ t - 1 := by
  classical
  rw [Fintype.card_subtype]
  simp_rw [Finset.nonempty_iff_ne_empty]
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp [Fintype.card_finset]
end PermanentRollout
