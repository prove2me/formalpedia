-- Prove2me | solution 1 for Scott1972.ContinuousLattice.IsContinuousLatticeProjection.incl_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:40:12.30548+00:00
-- url     : https://prove2.me/submissions/3c4ee4b3-5e8a-401f-8aa3-1814038cfcbe

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeProjection_retr_bot

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
open Finset
open Scott1972.ContinuousLattice.IsContinuousLatticeProjection
namespace Scott1972.ContinuousLattice.IsContinuousLatticeProjection
theorem _root_.solution (P : IsContinuousLatticeProjection D D') : P.incl (⊥ : D) = ⊥ :=
  le_antisymm (by simpa [retr_bot P] using P.incl_retr_le (⊥ : D')) bot_le
end Scott1972.ContinuousLattice.IsContinuousLatticeProjection
