-- Prove2me | solution 1 for Scott1972.ContinuousLattice.ScottOpen.isUpperSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:33:50.786201+00:00
-- url     : https://prove2.me/submissions/a9cd534f-9ff8-4ed3-b2c9-e9f769d6d68f

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
namespace ScottOpen
theorem _root_.solution {U : Set D} (h : ScottOpen U) : IsUpperSet U := h.1
end ScottOpen
end Scott1972.ContinuousLattice
