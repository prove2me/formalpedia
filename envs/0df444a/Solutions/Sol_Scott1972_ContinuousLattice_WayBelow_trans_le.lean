-- Prove2me | solution 1 for Scott1972.ContinuousLattice.WayBelow.trans_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:28:20.69034+00:00
-- url     : https://prove2.me/submissions/06898225-e4a9-4847-a4b6-4b7d15e90e14

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
namespace WayBelow
theorem _root_.solution {x y z : D} (h : x ≪ y) (hyz : y ≤ z) : x ≪ z := by
  obtain ⟨U, hU, hyU, hsub⟩ := h
  exact ⟨U, hU, hU.1 hyz hyU, hsub⟩
end WayBelow
end Scott1972.ContinuousLattice
