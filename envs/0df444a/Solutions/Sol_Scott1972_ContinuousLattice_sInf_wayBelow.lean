-- Prove2me | solution 1 for Scott1972.ContinuousLattice.sInf_wayBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:30:56.313339+00:00
-- url     : https://prove2.me/submissions/23368d94-b12e-4f8b-82d4-7a4eb5c67c5c

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution {U : Set D} (hU : ScottOpen U) {y : D} (hy : y ∈ U) :
    sInf U ≪ y :=
  ⟨U, hU, hy, fun _ hz => Set.mem_Ici.2 (sInf_le hz)⟩
end Scott1972.ContinuousLattice
