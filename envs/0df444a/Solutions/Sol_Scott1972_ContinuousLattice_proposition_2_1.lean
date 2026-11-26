-- Prove2me | solution 1 for Scott1972.ContinuousLattice.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:42:42.724013+00:00
-- url     : https://prove2.me/submissions/aa959ede-45f1-48fd-b4a8-24b0e1d46d05

import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.DirSupClosed
import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_1_of_le
import Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_1_le_of_converges

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]
variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
variable {x : ι → D} {L y : D}
namespace Scott1972.ContinuousLattice
theorem _root_.solution [Nonempty ι] (hx : IsMonotoneNet x) (hL : IsLUB (range x) L) :
    ScottConvergesTo x y ↔ y ≤ L :=
  ⟨fun hconv => proposition_2_1_le_of_converges hL hconv, proposition_2_1_of_le hx hL⟩
end Scott1972.ContinuousLattice
