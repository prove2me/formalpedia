-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottFunctionSubbasis_isOpen_scott
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:38:54.950684+00:00
-- url     : https://prove2.me/submissions/0633a8a2-3945-4abc-b810-803f69c7c567

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
namespace Scott1972.ContinuousLattice
theorem _root_.solution {x : D} {U : Set D'} (hU : @IsOpen D' scottTopologicalSpace U) :
    @IsOpen (ScottC D D') (@scottFunctionTopology D D' scottTopologicalSpace scottTopologicalSpace)
      {f : ScottC D D' | f x ∈ U} :=
  isOpen_generateFrom_of_mem (s := {f : ScottC D D' | f x ∈ U}) ⟨x, U, hU, rfl⟩
end Scott1972.ContinuousLattice
