-- Prove2me | solution 1 for Scott1972.ContinuousLattice.lemma_3_9_retr_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:45:57.84656+00:00
-- url     : https://prove2.me/submissions/cf255774-9c68-451a-9542-dc44d0a00d0e

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_scottSubspaceExtendInf_mono_retr

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
theorem _root_.solution {e : X → Y} (P : IsContinuousLatticeProjection D D') {g : X → D'}
    (U : Set Y) :
    P.retr (scottSubspaceExtendInf e g U) ≤ scottSubspaceExtendInf e (fun x => P.retr (g x)) U :=
  scottSubspaceExtendInf_mono_retr (e := e) (g := g) P U
end Scott1972.ContinuousLattice
