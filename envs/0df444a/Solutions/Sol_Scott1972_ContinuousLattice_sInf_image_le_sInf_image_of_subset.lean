-- Prove2me | solution 1 for Scott1972.ContinuousLattice.sInf_image_le_sInf_image_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:40:14.189811+00:00
-- url     : https://prove2.me/submissions/17197799-1327-4efc-857f-8100ac85d3dc

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
theorem _root_.solution {α : Type*} {f : α → D} {S T : Set α}
    (hST : S ⊆ T) : sInf (Set.image f T) ≤ sInf (Set.image f S) :=
  sInf_le_sInf fun _ hd => by
    obtain ⟨s, hs, rfl⟩ := hd
    exact ⟨s, hST hs, rfl⟩
end Scott1972.ContinuousLattice
