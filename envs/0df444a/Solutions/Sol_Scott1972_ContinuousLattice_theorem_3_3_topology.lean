-- Prove2me | solution 1 for Scott1972.ContinuousLattice.theorem_3_3_topology
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:39:33.343357+00:00
-- url     : https://prove2.me/submissions/6d8f5ac6-12ea-4702-b4b8-e18a0fbab252

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_stepMap_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_theorem_3_3_isContinuousLattice
import Theorems.Thm_Scott1972_ContinuousLattice_wayBelow_finset_sup
import Theorems.Thm_Scott1972_ContinuousLattice_pointwiseSubbasic_isOpen
import Theorems.Thm_Scott1972_ContinuousLattice_pointwiseSubbasic_scottOpen
import Theorems.Thm_Scott1972_ContinuousLattice_wayBelow_le_finset_sup_step
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le_trans
import Theorems.Thm_Scott1972_ContinuousLattice_exists_wayBelow_subset
import Theorems.Thm_Scott1972_ContinuousLattice_isOpen_iff_scottOpen
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
theorem _root_.solution (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) = scottMapPointwiseTopology D D' := by
  have hL : IsContinuousLattice (ScottMap D D') := theorem_3_3_isContinuousLattice hD hD'
  apply le_antisymm
  · -- pointwise ⊆ Scott: each subbasic set is Scott-open in the lattice
    apply le_generateFrom_iff_subset_isOpen.2
    rintro W ⟨x, U, hUopen, rfl⟩
    exact isOpen_iff_scottOpen.mpr (pointwiseSubbasic_scottOpen x (isOpen_iff_scottOpen.mp hUopen))
  · -- Scott ⊆ pointwise: each Scott-open lattice set is pointwise-open, via the `↟φ` basis
    intro U hU
    rw [isOpen_iff_scottOpen] at hU
    rw [@isOpen_iff_forall_mem_open (ScottMap D D') (scottMapPointwiseTopology D D')]
    intro g hgU
    obtain ⟨φ, hφg, hφsub⟩ := exists_wayBelow_subset hL hU hgU
    obtain ⟨F, hF, hφF⟩ := wayBelow_le_finset_sup_step hD hD' hφg
    refine ⟨⋂ p ∈ F, {h : ScottMap D D' | (p.2 : D') ≪ (h : D → D') p.1}, ?_, ?_, ?_⟩
    · intro h hh
      refine hφsub (WayBelow.le_trans hφF (wayBelow_finset_sup fun p hp => ?_))
      exact stepMap_wayBelow (Set.mem_iInter₂.1 hh p hp)
    · exact @isOpen_biInter_finset (ScottMap D D') (D × D') (scottMapPointwiseTopology D D') F _
        (fun p _ => pointwiseSubbasic_isOpen p.1 (isOpen_iff_scottOpen.mpr (scottOpen_wayBelow p.2)))
    · exact Set.mem_iInter₂.2 fun p hp => hF p hp
end Scott1972.ContinuousLattice
