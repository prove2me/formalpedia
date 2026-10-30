-- Prove2me | solution 1 for WilliamsonShmoys.planar_strict_extension_of_disconnected_drawing__p2m_5b4ba625_e76a_490b_a06e_75a37c9ee7a0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:18:15.638238+00:00
-- url     : https://prove2.me/submissions/36c78b7f-72e1-46da-a7ab-b42ac93cea1f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_separated_vertices_of_disconnected__p2m_0bc9c97a_babf_49ce_aa25_e06a76bb47e2_a2
import Theorems.Thm_WilliamsonShmoys_planar_bridge_extension__p2m_0bc9c97a_babf_49ce_aa25_e06a76bb47e2_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V)
    (hdisc : Not G.Connected) :
    Exists fun K : SimpleGraph V => And (LE.le G K) (And (Not (G = K)) (HasPlanarDrawingOn K)) := by
  obtain ⟨u, v, huv, hnotreach⟩ :=
    WilliamsonShmoys.exists_separated_vertices_of_disconnected__p2m_0bc9c97a_babf_49ce_aa25_e06a76bb47e2_a2 G hV hdisc
  exact WilliamsonShmoys.planar_bridge_extension__p2m_0bc9c97a_babf_49ce_aa25_e06a76bb47e2_a2 G hG u v huv hnotreach