-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_e2b82d88_2bbb_4150_bc2f_79d38f5c0ef7_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:28:34.731766+00:00
-- url     : https://prove2.me/submissions/7923342a-18e6-48fe-8948-e64f6908f8ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_6301d38c_0224_4362_a676_de729a46b58e_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6301d38c_0224_4362_a676_de729a46b58e_a3
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hNcount, hK, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_6301d38c_0224_4362_a676_de729a46b58e_a3
      N hN
  have hKcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_6301d38c_0224_4362_a676_de729a46b58e_a3
      K hK hCard hMax
  omega