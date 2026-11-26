-- Prove2me | solution 1 for Scott1972.ContinuousLattice.IsContinuousLatticeRetraction.retr_wayBelow_of_wayBelow_incl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:39:17.175622+00:00
-- url     : https://prove2.me/submissions/2c63c882-b10b-4b30-b5d0-95e909e31b79

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeRetraction_incl_preservesDirectedSup
import Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_preimage


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
open Scott1972.ContinuousLattice.IsContinuousLatticeRetraction
namespace Scott1972.ContinuousLattice.IsContinuousLatticeRetraction
theorem _root_.solution (R : IsContinuousLatticeRetraction D D')
    {d : D} {x' : D'} (hx' : x' ≪ R.incl d) : R.retr x' ≪ d := by
  obtain ⟨U', hU'open, hd_in, hU'sub⟩ := hx'
  refine ⟨(R.incl : D → D') ⁻¹' U', scottOpen_preimage R.incl_preservesDirectedSup hU'open,
    hd_in, fun z hz => ?_⟩
  have hle : x' ≤ R.incl z := Set.mem_Ici.1 (hU'sub hz)
  have hjle := R.retr.monotone hle
  rw [R.retr_incl z] at hjle
  exact Set.mem_Ici.2 hjle
end Scott1972.ContinuousLattice.IsContinuousLatticeRetraction
