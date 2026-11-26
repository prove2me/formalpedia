-- Prove2me | solution 1 for Scott1972.ContinuousLattice.IsContinuousLatticeProjection.incl_finset_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:40:51.610059+00:00
-- url     : https://prove2.me/submissions/90816b76-6060-4d7b-b850-f1fe1d793f13

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeProjection_incl_bot
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeProjection_incl_sup
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_sup


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
theorem _root_.solution (P : IsContinuousLatticeProjection D D') (T : Finset D) :
    P.incl (T.sup (fun x => x)) = T.sup (fun x => P.incl x) := by
  classical
  refine Finset.induction_on T ?base ?step
  · simp only [sup_empty]
    exact incl_bot P
  · intro a s _ ih
    simp only [sup_insert]
    rw [incl_sup P, ih]
end Scott1972.ContinuousLattice.IsContinuousLatticeProjection
