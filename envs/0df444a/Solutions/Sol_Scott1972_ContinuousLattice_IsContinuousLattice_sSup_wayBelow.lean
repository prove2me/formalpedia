-- Prove2me | solution 1 for Scott1972.ContinuousLattice.IsContinuousLattice.sSup_wayBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:28:19.789819+00:00
-- url     : https://prove2.me/submissions/eb61fd92-8fe3-490a-9523-ea81b225c8e6

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
namespace IsContinuousLattice
theorem _root_.solution (h : IsContinuousLattice D) (y : D) :
    sSup {x | x ≪ y} = y :=
  (h y).sSup_eq
end IsContinuousLattice
end Scott1972.ContinuousLattice
