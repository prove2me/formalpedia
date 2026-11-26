-- Prove2me | solution 1 for Scott1972.ContinuousLattice.proposition_3_12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:45:58.712031+00:00
-- url     : https://prove2.me/submissions/3ce8ec0c-8880-4e1f-8618-bb0b886ef97b

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
theorem _root_.solution :
    (∀ T : Set (ScottMap D D), (∀ j ∈ T, IsProjection j) → IsProjection (sSup T))
      ∧ Nonempty (CompleteLattice (Projections D)) :=
  ⟨fun _ h => isProjection_sSup h, ⟨Projections.instCompleteLattice⟩⟩
end Scott1972.ContinuousLattice
