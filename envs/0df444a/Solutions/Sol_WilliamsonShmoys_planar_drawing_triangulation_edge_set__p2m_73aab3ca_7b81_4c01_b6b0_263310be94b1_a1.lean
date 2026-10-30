-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_edge_set__p2m_73aab3ca_7b81_4c01_b6b0_263310be94b1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:53:32.381935+00:00
-- url     : https://prove2.me/submissions/5251e1e6-b8c2-49b8-b30f-95fc8d33de5a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_6afd414e_9bd5_44bb_abb9_3ce14ecb25d9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_6afd414e_9bd5_44bb_abb9_3ce14ecb25d9_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ F : Finset (Sym2 V),
      G.edgeFinset ⊆ F ∧ F.card = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hdec, hsub, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6afd414e_9bd5_44bb_abb9_3ce14ecb25d9_a1
      G hG hcard
  letI : DecidableRel H.Adj := hdec
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6afd414e_9bd5_44bb_abb9_3ce14ecb25d9_a1
      H hH hmax hcard
  exact ⟨H.edgeFinset, hsub, hcount⟩