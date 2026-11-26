-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottSubspaceExtendInf_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:40:13.594561+00:00
-- url     : https://prove2.me/submissions/2c402764-6052-43a6-859f-866f716518c1

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
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y]
omit [TopologicalSpace Y]
namespace Scott1972.ContinuousLattice
theorem _root_.solution {f' : ScottMap Y D} {U : Set Y} {y : Y}
    (hyU : y ∈ U) : sInf (Set.image (f' : Y → D) U) ≤ f' y :=
  sInf_le (Set.mem_image_of_mem _ hyU)
end Scott1972.ContinuousLattice
