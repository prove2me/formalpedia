-- Prove2me | solution 1 for Scott1972.ContinuousLattice.IsContinuousLatticeProjection.retr_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:39:37.340586+00:00
-- url     : https://prove2.me/submissions/9a57af43-266a-43b8-ad1a-ae3d33495b95

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le_trans


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
theorem _root_.solution (P : IsContinuousLatticeProjection D D') : (P.retr : D' → D) ⊥ = ⊥ := by
  have hle : (⊥ : D') ≤ P.incl (⊥ : D) := bot_le
  have heq : (P.retr : D' → D) (P.incl (⊥ : D)) = (⊥ : D) := P.retr_incl (d := (⊥ : D))
  exact le_antisymm (le_trans (P.retr.monotone hle) (le_of_eq heq)) bot_le
end Scott1972.ContinuousLattice.IsContinuousLatticeProjection
