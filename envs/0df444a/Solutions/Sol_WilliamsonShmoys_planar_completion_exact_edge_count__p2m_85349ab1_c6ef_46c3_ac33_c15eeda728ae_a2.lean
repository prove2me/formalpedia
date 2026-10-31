-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_exact_edge_count__p2m_85349ab1_c6ef_46c3_ac33_c15eeda728ae_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:45:36.650764+00:00
-- url     : https://prove2.me/submissions/5ba465a4-f4e2-4233-9204-86df299b9448

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_0b759ff7_c54c_46d9_9040_98bf9ecec633_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_0b759ff7_c54c_46d9_9040_98bf9ecec633_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_0b759ff7_c54c_46d9_9040_98bf9ecec633_a1
      G hG
  have hcount :=
    WilliamsonShmoys_maximal_planar_edge_count__p2m_0b759ff7_c54c_46d9_9040_98bf9ecec633_a1
      H hH hV hmax
  exact ⟨H, hGH, hH, hcount⟩