-- Prove2me | solution 1 for Scott1972.ContinuousLattice.IsContinuousLatticeRetraction.image_retr_wayBelow_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:39:20.00536+00:00
-- url     : https://prove2.me/submissions/6dd1fcbc-3441-4eae-8a82-5e68312bce39

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_bot_wayBelow


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
theorem _root_.solution (R : IsContinuousLatticeRetraction D D') (d : D) :
    (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}).Nonempty :=
  ⟨R.retr ⊥, ⊥, bot_wayBelow _, rfl⟩
end Scott1972.ContinuousLattice.IsContinuousLatticeRetraction
