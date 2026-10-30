-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:02:45.363204+00:00
-- url     : https://prove2.me/submissions/ac461a4a-f0a1-44b8-a5f5-55348a19edd0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_when_disconnected__p2m_0eaeae48_ca39_4818_a504_bddb7c4b7de2_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_of_finite_strict_augmentation__p2m_0eaeae48_ca39_4818_a504_bddb7c4b7de2_a2
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, L ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  apply WilliamsonShmoys.planar_drawing_connected_supergraph_of_finite_strict_augmentation__p2m_0eaeae48_ca39_4818_a504_bddb7c4b7de2_a2
    L hL hCard
  intro G hLG hG hDisc
  exact WilliamsonShmoys.planar_drawing_add_edge_when_disconnected__p2m_0eaeae48_ca39_4818_a504_bddb7c4b7de2_a2
    G hG hDisc