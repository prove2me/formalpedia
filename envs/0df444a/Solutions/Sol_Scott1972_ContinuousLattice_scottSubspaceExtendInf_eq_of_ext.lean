-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottSubspaceExtendInf_eq_of_ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:40:32.724504+00:00
-- url     : https://prove2.me/submissions/763413cb-f509-4d2e-8166-45fa23671cb3

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
namespace Scott1972.ContinuousLattice
theorem _root_.solution {e : X → Y} {f g' : X → D} (h : ∀ x, f x = g' x) (U : Set Y) :
    scottSubspaceExtendInf e f U = scottSubspaceExtendInf e g' U := by
  unfold scottSubspaceExtendInf
  congr 1
  ext d
  simp [Set.mem_image, Set.mem_preimage, h]
end Scott1972.ContinuousLattice
