-- Prove2me | solution 1 for WilliamsonShmoys.planar_add_edge_between_unreachable_vertices__p2m_806ab279_09f1_47fe_9b7f_fe9caced9bd3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:40:44.166193+00:00
-- url     : https://prove2.me/submissions/1ec70db4-7043-492e-9b7d-1f69d42539d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_single_edge_extension__p2m_c8d20c40_a498_43d8_b4ed_abd0723d73a4_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (u v : V)
    (hdisj : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ H.Adj u v := by
  obtain ⟨H, hsub, hplanar, hedge⟩ :=
    WilliamsonShmoys.planar_drawingOn_single_edge_extension__p2m_c8d20c40_a498_43d8_b4ed_abd0723d73a4_a1
      G hG u v hdisj
  have huv : H.Adj u v := (hedge u v).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
  exact ⟨H, hsub, hplanar, huv⟩