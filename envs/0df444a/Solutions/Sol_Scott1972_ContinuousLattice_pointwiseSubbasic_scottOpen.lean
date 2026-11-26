-- Prove2me | solution 1 for Scott1972.ContinuousLattice.pointwiseSubbasic_scottOpen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:38:45.423342+00:00
-- url     : https://prove2.me/submissions/cfd09f45-7926-47fd-8550-8beeae1a78b3

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
namespace Scott1972.ContinuousLattice
theorem _root_.solution (x : D) {U : Set D'} (hU : ScottOpen U) :
    ScottOpen {f : ScottMap D D' | (f : D → D') x ∈ U} := by
  refine ⟨fun f f' hff' hf => hU.1 (hff' x) hf, fun F hFne hFdir hmem => ?_⟩
  simp only [Set.mem_setOf_eq, ScottMap.sSup_apply] at hmem
  have hne : (Set.image (fun g : ScottMap D D' => (g : D → D') x) F).Nonempty := hFne.image _
  have hdir : DirectedOn (· ≤ ·) (Set.image (fun g : ScottMap D D' => (g : D → D') x) F) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hFdir a ha b hb
    exact ⟨(c : D → D') x, Set.mem_image_of_mem _ hc, hac x, hbc x⟩
  obtain ⟨_, ⟨g, hgF, rfl⟩, hg⟩ := hU.2 hne hdir hmem
  exact ⟨g, hgF, hg⟩
end Scott1972.ContinuousLattice
