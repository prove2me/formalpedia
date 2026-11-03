-- Prove2me | solution 2 for WilliamsonShmoys.maximalPlanarDrawingOn_edge_count_lower__p2m_10767c1e_3761_455c_b81d_2c159386481f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:47:25.293963+00:00
-- url     : https://prove2.me/submissions/83c6c0a5-d057-41e2-a9d2-cf149b9ff240

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_1095f796_c580_4096_843f_cd051f083539_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_1095f796_c580_4096_843f_cd051f083539_a1 K hCard hK hmax