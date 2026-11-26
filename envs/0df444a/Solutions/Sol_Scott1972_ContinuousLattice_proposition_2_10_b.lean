-- Prove2me | solution 1 for Scott1972.ContinuousLattice.proposition_2_10_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:40:00.853097+00:00
-- url     : https://prove2.me/submissions/52611972-37be-47bd-8ac7-644dde16fd2a

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeRetraction_incl_preservesDirectedSup
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeRetraction_sSup_image_retr_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeRetraction_image_retr_wayBelow_nonempty
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeRetraction_image_retr_wayBelow_directed
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le
import Theorems.Thm_Scott1972_ContinuousLattice_isOpen_iff_scottOpen
import Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_preimage
import Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_wayBelow


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
namespace Scott1972.ContinuousLattice
theorem _root_.solution (R : IsContinuousLatticeRetraction D D')
    (hD' : IsContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace D) =
      TopologicalSpace.induced (R.incl : D → D') scottTopologicalSpace := by
  apply le_antisymm
  · intro U hU
    rw [isOpen_induced_iff (t := scottTopologicalSpace)] at hU
    obtain ⟨V', hV'open, rfl⟩ := hU
    rw [isOpen_iff_scottOpen] at hV'open ⊢
    exact scottOpen_preimage R.incl_preservesDirectedSup hV'open
  · intro U hU
    rw [isOpen_iff_scottOpen] at hU
    rw [@isOpen_iff_forall_mem_open _
      (TopologicalSpace.induced (R.incl : D → D') scottTopologicalSpace)]
    intro d hd
    have hmem : sSup (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}) ∈ U := by
      rw [R.sSup_image_retr_wayBelow hD' d]; exact hd
    obtain ⟨p, hp, hpU⟩ :=
      hU.2 (R.image_retr_wayBelow_nonempty d) (R.image_retr_wayBelow_directed d) hmem
    obtain ⟨x', hx', rfl⟩ := hp
    refine ⟨(R.incl : D → D') ⁻¹' {z' | x' ≪ z'}, fun z hz => ?_, ?_, hx'⟩
    · have hjle := R.retr.monotone (show x' ≤ R.incl z from (hz : x' ≪ R.incl z).le)
      rw [R.retr_incl z] at hjle
      exact hU.1 hjle hpU
    · rw [isOpen_induced_iff (t := scottTopologicalSpace)]
      exact ⟨{z' | x' ≪ z'}, isOpen_iff_scottOpen.mpr (scottOpen_wayBelow x'), rfl⟩
end Scott1972.ContinuousLattice
