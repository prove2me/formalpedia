-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_component_partition_edge_bounds__p2m_fd05939c_3060_4687_b686_08bcaa4f6cdd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:30:24.193204+00:00
-- url     : https://prove2.me/submissions/af21401a-8697-45e8-8a32-2e64a1f4c58d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_component_partition_accounting__p2m_e7b88b3e_57d2_4e16_879b_dc797a764fee_a1
import Theorems.Thm_WilliamsonShmoys_planar_induced_edge_bound__p2m_e7b88b3e_57d2_4e16_879b_dc797a764fee_a1

set_option autoImplicit false

open Finset

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ C : V → Finset V,
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (Finset.univ.biUnion C = Finset.univ) ∧
      (L.edgeSet.ncard = ∑ i : V, (L.induce (fun v => v ∈ C i)).edgeSet.ncard) ∧
      (∀ i,
        if 3 ≤ (C i).card then
          (L.induce (fun v => v ∈ C i)).edgeSet.ncard ≤ 3 * (C i).card - 6
        else if 2 ≤ (C i).card then
          (L.induce (fun v => v ∈ C i)).edgeSet.ncard ≤ 1
        else
          (L.induce (fun v => v ∈ C i)).edgeSet.ncard = 0) := by
  obtain ⟨C, hdisjoint, hcover, hedge_count⟩ :=
    WilliamsonShmoys.planar_component_partition_accounting__p2m_e7b88b3e_57d2_4e16_879b_dc797a764fee_a1 L
  refine ⟨C, hdisjoint, hcover, hedge_count, ?_⟩
  intro i
  exact WilliamsonShmoys.planar_induced_edge_bound__p2m_e7b88b3e_57d2_4e16_879b_dc797a764fee_a1
    L hL (C i)