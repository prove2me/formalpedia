-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottSubspaceExtendInf_eq_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:40:19.380434+00:00
-- url     : https://prove2.me/submissions/ec12d07b-f0a9-47e5-af5b-eda6cd9c41e1

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
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y]
namespace Scott1972.ContinuousLattice
theorem _root_.solution {e : X → Y} {f : X → D} {U : Set Y}
    (f' : ScottMap Y D) (h : ∀ x, f' (e x) = f x) :
    scottSubspaceExtendInf e f U = sInf (Set.image (f' : Y → D) (Set.image e Set.univ ∩ U)) := by
  have hset : f '' (e ⁻¹' U) = Set.image (f' : Y → D) (Set.image e Set.univ ∩ U) := by
    ext d
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Set.mem_univ, true_and]
    constructor
    · rintro ⟨x, hxU, heq⟩
      refine ⟨e x, ⟨?_, hxU⟩, ?_⟩
      · exact ⟨x, rfl⟩
      · rw [h x, heq]
    · rintro ⟨y, ⟨hex, hyU⟩, heq⟩
      obtain ⟨x, _, rfl⟩ := hex
      exact ⟨x, hyU, (h x).symm.trans heq⟩
  rw [scottSubspaceExtendInf, hset]
end Scott1972.ContinuousLattice
