-- Prove2me | solution 1 for Scott1972.ContinuousLattice.IsContinuousLatticeProjection.proposition_3_10_forward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:45:49.109978+00:00
-- url     : https://prove2.me/submissions/c5abc80b-d282-44a4-854e-6d64650edb75

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeProjection_incl_injective
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeProjection_incl_sSup
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeProjection_incl_wayBelow

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
theorem _root_.solution (P : IsContinuousLatticeProjection D D')
    (hD' : IsContinuousLattice D') :
    (∀ S : Set D, (P.incl : D → D') (sSup S) = sSup (Set.image (P.incl : D → D') S))
      ∧ Function.Injective (P.incl : D → D')
      ∧ (∀ x y : D, x ≪ y → (P.incl : D → D') x ≪ (P.incl : D → D') y) :=
  ⟨fun S => P.incl_sSup S, fun _ _ h => P.incl_injective h,
    fun _ _ h => P.incl_wayBelow hD' h⟩
end Scott1972.ContinuousLattice.IsContinuousLatticeProjection
