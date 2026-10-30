-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_04736d40_a8e2_4a01_9968_14670118dd12_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:00:53.487174+00:00
-- url     : https://prove2.me/submissions/767ee31c-e0c3-440f-8a82-d2e0e17cf5f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_f9dc181e_d230_4644_be1b_965b4f83a602_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_f9dc181e_d230_4644_be1b_965b4f83a602_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : LE.le 3 (Fintype.card V))
    (hmax : (L : SimpleGraph V) -> LE.le K L -> HasPlanarDrawingOn L -> LE.le L K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hu := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_f9dc181e_d230_4644_be1b_965b4f83a602_a2 K hK hV
  have hl := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f9dc181e_d230_4644_be1b_965b4f83a602_a2 K hK hV hmax
  omega
