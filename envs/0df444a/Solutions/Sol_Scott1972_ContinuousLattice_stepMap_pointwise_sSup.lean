-- Prove2me | solution 1 for Scott1972.ContinuousLattice.stepMap_pointwise_sSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:35:41.525512+00:00
-- url     : https://prove2.me/submissions/e7ead5b2-ddfb-4b1b-91c7-8e44617fbc23

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLattice_sSup_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le
import Theorems.Thm_Scott1972_ContinuousLattice_bot_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_directedOn_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_wayBelow_sSup_iff


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D')
    (f : ScottMap D D') (x : D) :
    sSup {e' : D' | ∃ e, e ≪ x ∧ e' ≪ (f : D → D') e} = (f : D → D') x := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro e' ⟨e, hex, he'⟩
    exact he'.le.trans (f.monotone hex.le)
  · rw [← hD'.sSup_wayBelow ((f : D → D') x)]
    refine sSup_le ?_
    intro w hw
    have hfx : (f : D → D') x = sSup (Set.image (f : D → D') {e | e ≪ x}) := by
      rw [← f.preservesDirectedSup_coe {e | e ≪ x} ⟨⊥, bot_wayBelow x⟩ (directedOn_wayBelow x),
        hD.sSup_wayBelow x]
    rw [hfx] at hw
    have hne : (Set.image (f : D → D') {e | e ≪ x}).Nonempty := ⟨f ⊥, ⊥, bot_wayBelow x, rfl⟩
    have hdir : DirectedOn (· ≤ ·) (Set.image (f : D → D') {e | e ≪ x}) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨c, hc, hac, hbc⟩ := directedOn_wayBelow x a ha b hb
      exact ⟨f c, Set.mem_image_of_mem _ hc, f.monotone hac, f.monotone hbc⟩
    obtain ⟨_, ⟨e, hex, rfl⟩, hwe⟩ := (wayBelow_sSup_iff hne hdir).1 hw
    exact le_sSup ⟨e, hex, hwe⟩
end Scott1972.ContinuousLattice
