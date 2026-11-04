-- Prove2me | solution 1 for WilliamsonShmoys.subgraph_of_maximal_planar_drawing_obeys_edge_bound__p2m_40c1c52c_c498_4287_a557_1efecd0d6ca7_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:02:14.68128+00:00
-- url     : https://prove2.me/submissions/65ee8feb-186b-49dc-8f56-950d98d1b933

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_planar_edge_count__p2m_0c1d2833_de32_49c5_aebf_88ae0a9260a2_a1
import Theorems.Thm_WilliamsonShmoys_subgraph_edgeFinset_card_mono__p2m_0c1d2833_de32_49c5_aebf_88ae0a9260a2_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hsub : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  have h_exact := WilliamsonShmoys.maximal_drawable_graph_has_planar_edge_count__p2m_0c1d2833_de32_49c5_aebf_88ae0a9260a2_a1
    H hcard hH hmax
  have h_mono := WilliamsonShmoys.subgraph_edgeFinset_card_mono__p2m_0c1d2833_de32_49c5_aebf_88ae0a9260a2_a1
    G H hsub
  omega