-- Prove2me | solution 1 for Scott1972.ContinuousLattice.ScottMap.continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:34:57.671369+00:00
-- url     : https://prove2.me/submissions/ae30571d-e9de-4a03-9357-20fedd24cfdf

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
open Scott1972.ContinuousLattice.ScottMap
namespace Scott1972.ContinuousLattice.ScottMap
theorem _root_.solution (f : ScottMap D D') :
    @Continuous D D' scottTopologicalSpace scottTopologicalSpace f :=
  f.2
end Scott1972.ContinuousLattice.ScottMap
