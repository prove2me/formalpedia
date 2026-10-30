-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_ec87327c_94d1_4f33_a35a_c8476e7ad1f3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:07:35.875493+00:00
-- url     : https://prove2.me/submissions/2e40a647-436d-4cf6-9714-f9239ccc0ae0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_97ea1df5_d556_4f68_a658_dec2bacf773d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_97ea1df5_d556_4f68_a658_dec2bacf773d_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H) (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKDraw, hMax⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_97ea1df5_d556_4f68_a658_dec2bacf773d_a1 H hDraw
  exact ⟨K, hHK, hKDraw, WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_97ea1df5_d556_4f68_a658_dec2bacf773d_a1 K hKDraw hCard hMax⟩
