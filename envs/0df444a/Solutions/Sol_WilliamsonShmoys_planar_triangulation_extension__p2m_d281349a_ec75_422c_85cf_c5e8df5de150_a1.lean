-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_d281349a_ec75_422c_85cf_c5e8df5de150_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:30:40.197093+00:00
-- url     : https://prove2.me/submissions/162a5acb-8067-49f3-8f0e-6bac5ba47813
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_maximal_extension__p2m_160c891e_c18d_4863_b495_0a238ee51219_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_edge_maximal__p2m_160c891e_c18d_4863_b495_0a238ee51219_a1
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_instance_irrel__p2m_160c891e_c18d_4863_b495_0a238ee51219_a3

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       letI : Fintype ↑N.edgeSet := N.fintypeEdgeSet
       3 * Fintype.card V ≤ N.edgeFinset.card + 6) := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_drawable_edge_maximal_extension__p2m_160c891e_c18d_4863_b495_0a238ee51219_a1 M hM
  refine ⟨N, hMN, hN, ?_⟩
  have hbound :=
    WilliamsonShmoys.planar_edge_bound_of_edge_maximal__p2m_160c891e_c18d_4863_b495_0a238ee51219_a1 N hN hV hmax
  have hcard :=
    WilliamsonShmoys.edgeFinset_card_instance_irrel__p2m_160c891e_c18d_4863_b495_0a238ee51219_a3 N
  rw [hcard] at hbound
  exact hbound