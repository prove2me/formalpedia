-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottFunctionTopology_eq_induced_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:44:00.592809+00:00
-- url     : https://prove2.me/submissions/255e16a5-82ad-4d59-a7d3-3f2dd1ea4bc4

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_scottFunctionSubbasis_isOpen

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
namespace Scott1972.ContinuousLattice
theorem _root_.solution (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] :
    scottFunctionTopology X Y = continuousMapInducedPiTopology X Y := by
  apply le_antisymm
  · letI : TopologicalSpace C(X, Y) := scottFunctionTopology X Y
    change scottFunctionTopology X Y ≤ continuousMapInducedPiTopology X Y
    rw [← continuous_iff_le_induced]
    exact continuous_pi fun x =>
      continuous_def.2 fun U hU =>
        scottFunctionSubbasis_isOpen (X := X) (Y := Y) (x := x) hU
  · apply le_generateFrom_iff_subset_isOpen.2
    rintro W ⟨x, U, hU, rfl⟩
    change @IsOpen C(X, Y)
      (TopologicalSpace.induced (fun f : C(X, Y) => (f : X → Y))
        (@Pi.topologicalSpace X (fun _ => Y) (fun _ => inferInstance)))
      {f : C(X, Y) | f x ∈ U}
    rw [isOpen_induced_iff]
    exact ⟨{g : X → Y | g x ∈ U}, (@continuous_apply X (fun _ => Y)
      (fun _ => inferInstance) x).isOpen_preimage U hU, rfl⟩
end Scott1972.ContinuousLattice
