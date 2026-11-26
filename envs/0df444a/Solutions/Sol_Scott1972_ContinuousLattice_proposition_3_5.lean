-- Prove2me | solution 1 for Scott1972.ContinuousLattice.proposition_3_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:44:31.735283+00:00
-- url     : https://prove2.me/submissions/8f935f88-d572-40f5-a92c-1cf433d80712

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_proposition_3_5_preservesDirectedSup
import Theorems.Thm_Scott1972_ContinuousLattice_continuous_of_preservesDirectedSup


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
    @Continuous (ScottMap (D × D') D'') (ScottMap D (ScottMap D' D''))
      scottTopologicalSpace scottTopologicalSpace scottLambda :=
  continuous_of_preservesDirectedSup proposition_3_5_preservesDirectedSup
end Scott1972.ContinuousLattice
