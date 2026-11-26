-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottMapPointwiseTopology_eq_induced_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:38:38.9848+00:00
-- url     : https://prove2.me/submissions/4f2b51d6-056c-4bc8-a2f0-a25a7f54f9ed

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_pointwiseSubbasic_isOpen

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
namespace Scott1972.ContinuousLattice
theorem _root_.solution :
    scottMapPointwiseTopology D D' = scottMapInducedPiTopology D D' := by
  apply le_antisymm
  · letI : TopologicalSpace D' := scottTopologicalSpace
    letI : TopologicalSpace (ScottMap D D') := scottMapPointwiseTopology D D'
    change scottMapPointwiseTopology D D' ≤ scottMapInducedPiTopology D D'
    rw [← continuous_iff_le_induced]
    exact continuous_pi fun x =>
      continuous_def.2 fun U hU => pointwiseSubbasic_isOpen (D := D) (D' := D') x hU
  · apply le_generateFrom_iff_subset_isOpen.2
    rintro W ⟨x, U, hU, rfl⟩
    letI : TopologicalSpace D' := scottTopologicalSpace
    change @IsOpen (ScottMap D D')
      (TopologicalSpace.induced (fun f : ScottMap D D' => (f : D → D'))
        (@Pi.topologicalSpace D (fun _ => D') (fun _ => scottTopologicalSpace)))
      {f : ScottMap D D' | (f : D → D') x ∈ U}
    rw [isOpen_induced_iff]
    exact ⟨{g : D → D' | g x ∈ U}, (@continuous_apply D (fun _ => D')
      (fun _ => scottTopologicalSpace) x).isOpen_preimage U hU, rfl⟩
end Scott1972.ContinuousLattice
