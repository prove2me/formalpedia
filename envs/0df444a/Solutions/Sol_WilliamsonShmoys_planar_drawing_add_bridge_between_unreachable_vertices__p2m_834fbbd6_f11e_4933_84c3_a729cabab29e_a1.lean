-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_bridge_between_unreachable_vertices__p2m_834fbbd6_f11e_4933_84c3_a729cabab29e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:55:34.651437+00:00
-- url     : https://prove2.me/submissions/005953ad-00ab-458c-9a10-14c34d563a74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_setup_of_unreachable__p2m_6b761602_ec4e_4b71_82d8_bcea18a590f0_a3
import Theorems.Thm_WilliamsonShmoys_planar_drawing_union_of_bridge_setup__p2m_6b761602_ec4e_4b71_82d8_bcea18a590f0_a3

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (u v : V) (hnot : ¬ H.Reachable u v) :
    HasPlanarDrawingOn
      (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) := by
  exact WilliamsonShmoys.planar_drawing_union_of_bridge_setup__p2m_6b761602_ec4e_4b71_82d8_bcea18a590f0_a3
    H u v
    (WilliamsonShmoys.planar_drawing_bridge_setup_of_unreachable__p2m_6b761602_ec4e_4b71_82d8_bcea18a590f0_a3
      H hH u v hnot)