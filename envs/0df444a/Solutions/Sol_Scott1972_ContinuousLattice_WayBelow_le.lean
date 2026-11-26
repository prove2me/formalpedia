-- Prove2me | solution 1 for Scott1972.ContinuousLattice.WayBelow.le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:28:08.560542+00:00
-- url     : https://prove2.me/submissions/18a8d34f-f9b1-4461-ac4f-cb63aac8b680

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
theorem _root_.solution {x y : D} (h : x ≪ y) : x ≤ y := by
  obtain ⟨U, _, hyU, hsub⟩ := h
  exact hsub hyU
end WayBelow
end Scott1972.ContinuousLattice
