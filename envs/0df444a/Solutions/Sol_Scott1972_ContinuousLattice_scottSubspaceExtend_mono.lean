-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottSubspaceExtend_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:45:54.786244+00:00
-- url     : https://prove2.me/submissions/2e7d5b86-717f-48f3-909b-fc4bf0b095be

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_scottSubspaceExtendInf_mono
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le_trans


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
theorem _root_.solution {e : X → Y} {f g₀ : X → D} (hfg : ∀ x, f x ≤ g₀ x) (y : Y) :
    scottSubspaceExtend e f y ≤ scottSubspaceExtend e g₀ y := by
  apply sSup_le
  intro d hd
  obtain ⟨U, hUopen, hyU, rfl⟩ := hd
  have hmem : scottSubspaceExtendInf e g₀ U ∈
      { d | ∃ U, @IsOpen Y scottTopologicalSpace U ∧ y ∈ U ∧ d = scottSubspaceExtendInf e g₀ U } :=
    ⟨U, hUopen, hyU, rfl⟩
  exact le_trans (scottSubspaceExtendInf_mono hfg U) (le_sSup hmem)
end Scott1972.ContinuousLattice
