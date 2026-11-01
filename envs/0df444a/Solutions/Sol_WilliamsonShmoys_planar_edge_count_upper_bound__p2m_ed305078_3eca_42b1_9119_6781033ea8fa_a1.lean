-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_ed305078_3eca_42b1_9119_6781033ea8fa_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:02:48.735964+00:00
-- url     : https://prove2.me/submissions/e430a4d4-f0c2-4c1f-89ee-0f7f422034ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_extension__p2m_e52a5279_3bb4_4190_b470_b345cecfed03_a4
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count__p2m_e52a5279_3bb4_4190_b470_b345cecfed03_a4
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (dG : DecidableRel G.Adj)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG;
      G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  obtain ⟨H, hGH, hH⟩ :=
    WilliamsonShmoys.planar_edge_maximal_extension__p2m_e52a5279_3bb4_4190_b470_b345cecfed03_a4
      G hG
  exact WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_e52a5279_3bb4_4190_b470_b345cecfed03_a4
    G H hG hH hGH dG (Classical.decRel _) hcard
