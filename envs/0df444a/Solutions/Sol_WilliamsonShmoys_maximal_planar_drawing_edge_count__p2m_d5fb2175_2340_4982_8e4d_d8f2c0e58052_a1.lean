-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_d5fb2175_2340_4982_8e4d_d8f2c0e58052_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:58:17.258907+00:00
-- url     : https://prove2.me/submissions/d1d75555-e42d-4fc3-834e-739b5ec0bc82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_upper__p2m_df73036e_c174_45db_bb7e_bf898419f140_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_df73036e_c174_45db_bb7e_bf898419f140_a1

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) (hCard : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hLower := WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_df73036e_c174_45db_bb7e_bf898419f140_a1 H hDraw hMax hCard
  have hUpper := WilliamsonShmoys_maximal_planar_drawing_edge_count_upper__p2m_df73036e_c174_45db_bb7e_bf898419f140_a1 H hDraw hCard
  omega