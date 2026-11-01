-- Prove2me | solution 1 for WilliamsonShmoys_planar_graph_has_triangulated_completion__p2m_1313175c_9801_43ac_98ea_21e1b7fe79cc_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:19:09.657427+00:00
-- url     : https://prove2.me/submissions/5d84a888-e2b1-4b7a-bc99-37418358a35c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_completion__p2m_76432751_4a60_438b_af25_c322d55d602e_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_76432751_4a60_438b_af25_c322d55d602e_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, ∃ (dH : DecidableRel H.Adj),
      (letI : DecidableRel H.Adj := dH
       G.edgeFinset ⊆ H.edgeFinset ∧
         H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  rcases WilliamsonShmoys.planar_supergraph_maximal_completion__p2m_76432751_4a60_438b_af25_c322d55d602e_a2
      G hG hV with ⟨H, dH, hGH, hH, hmax⟩
  letI : DecidableRel H.Adj := dH
  refine ⟨H, dH, ?_⟩
  exact ⟨hGH,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_76432751_4a60_438b_af25_c322d55d602e_a2
      H hH hV hmax⟩