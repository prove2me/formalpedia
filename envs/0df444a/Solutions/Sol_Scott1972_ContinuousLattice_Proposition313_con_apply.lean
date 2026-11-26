-- Prove2me | solution 1 for Scott1972.ContinuousLattice.Proposition313.con_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:35:02.977382+00:00
-- url     : https://prove2.me/submissions/b49b0d87-2886-47f9-9ea1-9e463dda9e56

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
open Scott1972.ContinuousLattice.Proposition313
namespace Scott1972.ContinuousLattice.Proposition313
theorem _root_.solution (x y : D) : ((con x : ScottMap D D) : D → D) y = x := rfl
end Scott1972.ContinuousLattice.Proposition313
