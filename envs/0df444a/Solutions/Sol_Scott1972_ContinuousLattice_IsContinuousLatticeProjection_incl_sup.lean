-- Prove2me | solution 1 for Scott1972.ContinuousLattice.IsContinuousLatticeProjection.incl_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:39:37.836613+00:00
-- url     : https://prove2.me/submissions/2a8cc7ec-16fe-473e-b8a5-a12421c53b7a

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
theorem _root_.solution (P : IsContinuousLatticeProjection D D') (x y : D) :
    P.incl (x ⊔ y) = P.incl x ⊔ P.incl y := by
  apply le_antisymm
  · have hx : x ≤ P.retr (P.incl x ⊔ P.incl y) :=
      le_trans (le_of_eq (P.retr_incl x).symm) (P.retr.monotone le_sup_left)
    have hy : y ≤ P.retr (P.incl x ⊔ P.incl y) :=
      le_trans (le_of_eq (P.retr_incl y).symm) (P.retr.monotone le_sup_right)
    exact le_trans (P.incl.monotone (sup_le hx hy)) (P.incl_retr_le (P.incl x ⊔ P.incl y))
  · exact sup_le (P.incl.monotone le_sup_left) (P.incl.monotone le_sup_right)
end Scott1972.ContinuousLattice.IsContinuousLatticeProjection
