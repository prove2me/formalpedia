-- Prove2me | solution 1 for WilliamsonShmoys.drawable_edge_augmentation_below_planar_bound__p2m_54520c23_fb0c_40a7_a4c0_ad4b1f033824_a1__p2m_54520c23_fb0c_40a7_a4c0_ad4b1f033824_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:15:09.682301+00:00
-- url     : https://prove2.me/submissions/94feb0bc-6f23-4682-9b9b-ba578101e028

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation_20261026

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hsmall : (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.edgeFinset.card) <
      3 * Fintype.card V - 6) :
    ∃ K : SimpleGraph V, G ≤ K ∧ K ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hcardedge : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [G.edgeFinset_card]
    exact Set.fintypeCard_eq_ncard G.edgeSet
  exact WilliamsonShmoys.planar_drawing_edge_augmentation_20261026
    G hdraw hcard (by simpa only [hcardedge] using hsmall)
