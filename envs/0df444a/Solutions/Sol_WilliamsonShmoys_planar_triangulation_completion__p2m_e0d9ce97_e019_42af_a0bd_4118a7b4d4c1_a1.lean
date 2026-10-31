-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_e0d9ce97_e019_42af_a0bd_4118a7b4d4c1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:27:52.191399+00:00
-- url     : https://prove2.me/submissions/e58689a9-f12f-4b11-ad19-f1e8a1081e72
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_686fb965_c7d3_49a9_b66b_5594659aa3e2_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_686fb965_c7d3_49a9_b66b_5594659aa3e2_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel H.Adj := dH
     ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
       H <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
       (letI : DecidableRel L.Adj := dL
        L.edgeFinset.card = 3 * Fintype.card V - 6)) := by
  letI : DecidableRel H.Adj := dH
  obtain ⟨L, dL, hHL, hLplanar, hLmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_686fb965_c7d3_49a9_b66b_5594659aa3e2_a2
      H dH hH hcard
  letI : DecidableRel L.Adj := dL
  refine ⟨L, dL, hHL, hLplanar, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_686fb965_c7d3_49a9_b66b_5594659aa3e2_a2
    L dL hLplanar hcard hLmax