-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_e592f479_7758_40c0_97f7_ee5e29c0fee3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:54:16.890235+00:00
-- url     : https://prove2.me/submissions/28a68b94-e7bf-4d80-90da-7ffeca25c2fb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_maximal_extension__p2m_8348399b_8cb6_45dd_ab73_26e7cc43a44d_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hSub, hCardH⟩ :=
    WilliamsonShmoys.planar_drawing_edge_count_maximal_extension__p2m_8348399b_8cb6_45dd_ab73_26e7cc43a44d_a1 M hM hCard
  calc
    M.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono hSub
    _ = 3 * Fintype.card V - 6 := hCardH