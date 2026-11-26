-- Prove2me | solution 1 for Scott1972.ContinuousLattice.preservesDirectedSup_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:29:36.825881+00:00
-- url     : https://prove2.me/submissions/5df112c9-a21b-4936-a789-952e3309cc08

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le_trans


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
namespace Scott1972.ContinuousLattice
theorem _root_.solution {f : D → D'} (hf : PreservesDirectedSup f) :
    Monotone f := by
  intro x y hxy
  have hdir : DirectedOn (· ≤ ·) ({x, y} : Set D) := directedOn_pair hxy
  have hS : ({x, y} : Set D).Nonempty := ⟨x, Set.mem_insert _ _⟩
  have hsup : sSup ({x, y} : Set D) = y := by
    calc sSup ({x, y} : Set D) = x ⊔ y := sSup_pair
      _ = y := by apply le_antisymm; exact sup_le hxy le_rfl; exact le_sup_right
  have heq := hf hS hdir
  rw [hsup, Set.image_pair] at heq
  exact le_trans (le_sSup (Set.mem_insert _ _)) heq.symm.le
end Scott1972.ContinuousLattice
