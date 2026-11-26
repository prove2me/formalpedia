-- Prove2me | solution 1 for Scott1972.ContinuousLattice.theorem_3_3_isContinuousLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:37:02.523977+00:00
-- url     : https://prove2.me/submissions/e1a9da24-4c8b-42d3-916e-ae94a2afebe4

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_stepMap_apply_of_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_stepMap_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_stepMap_pointwise_sSup
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hD : IsContinuousLattice D)
    (hD' : IsContinuousLattice D') : IsContinuousLattice (ScottMap D D') := by
  intro f
  refine ⟨fun h hh => hh.le, fun g hg => ?_⟩
  rw [ScottMap.le_def]
  intro x
  rw [← stepMap_pointwise_sSup hD hD' f x]
  refine sSup_le ?_
  rintro e' ⟨e, hex, he'⟩
  have hle : stepMap e e' ≤ g := hg (stepMap_wayBelow he')
  have hx := (ScottMap.le_def.1 hle) x
  rwa [stepMap_apply_of_wayBelow hex] at hx
end Scott1972.ContinuousLattice
