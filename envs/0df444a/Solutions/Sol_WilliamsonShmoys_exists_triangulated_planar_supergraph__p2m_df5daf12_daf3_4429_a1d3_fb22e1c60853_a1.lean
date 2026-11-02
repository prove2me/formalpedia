-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_df5daf12_daf3_4429_a1d3_fb22e1c60853_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:04:33.182835+00:00
-- url     : https://prove2.me/submissions/9dbb5b3c-05d0-4c04-a4c9-9d4e828ab342
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_1b95303a_4f95_40e4_980b_ac53e8480e68_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_supergraph__p2m_1b95303a_4f95_40e4_980b_ac53e8480e68_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      H ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeFinset.card + 6 := by
  obtain ⟨K, dK, hHK, hKdraw, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_1b95303a_4f95_40e4_980b_ac53e8480e68_a1
      H hH
  obtain hcount :=
    WilliamsonShmoys.edge_count_of_maximal_planar_supergraph__p2m_1b95303a_4f95_40e4_980b_ac53e8480e68_a1
      K dK hKdraw hcard hmax
  exact ⟨K, dK, hHK, hKdraw, hcount⟩