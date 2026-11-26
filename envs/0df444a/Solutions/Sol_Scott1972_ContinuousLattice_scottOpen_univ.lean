-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottOpen_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:28:58.410747+00:00
-- url     : https://prove2.me/submissions/480ddf40-60ff-4408-90c1-3a7d95777072

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution : ScottOpen (Set.univ : Set D) := by
  refine ⟨isUpperSet_univ, fun S hS _ _ => ?_⟩
  obtain ⟨s, hs⟩ := hS
  exact ⟨s, hs, Set.mem_univ s⟩
end Scott1972.ContinuousLattice
