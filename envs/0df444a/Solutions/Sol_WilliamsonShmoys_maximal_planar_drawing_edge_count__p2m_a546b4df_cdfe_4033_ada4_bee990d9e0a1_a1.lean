-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_a546b4df_cdfe_4033_ada4_bee990d9e0a1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:24:02.93524+00:00
-- url     : https://prove2.me/submissions/5ad280d7-34f2-4857-a992-a25dba772028

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_50304f69_3f87_43f6_91bb_4f1f44440925_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_50304f69_3f87_43f6_91bb_4f1f44440925_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hDraw : HasPlanarDrawingOn S)
    (hV : 3 <= Fintype.card V)
    (hMax : ∀ T : SimpleGraph V, S ≤ T → HasPlanarDrawingOn T → T = S) :
    S.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_drawing_edge_bound__p2m_50304f69_3f87_43f6_91bb_4f1f44440925_a2 S hDraw hV
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_50304f69_3f87_43f6_91bb_4f1f44440925_a2 S hDraw hV hMax
  omega