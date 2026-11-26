-- Prove2me | solution 1 for Scott1972.ContinuousLattice.directedOn_wayBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:29:51.595868+00:00
-- url     : https://prove2.me/submissions/3a76a606-31b7-4c46-9ec7-317c6042f9b5

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_sup

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution (y : D) : DirectedOn (· ≤ ·) {x | x ≪ y} :=
  fun a ha b hb => ⟨a ⊔ b, ha.sup hb, le_sup_left, le_sup_right⟩
end Scott1972.ContinuousLattice
