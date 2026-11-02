-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_ed0fa66f_dbcb_4794_9398_c71658f4fffe_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:37:47.338073+00:00
-- url     : https://prove2.me/submissions/7e5d4c2c-eab5-4405-a80f-4f38f2d34ffc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_count__p2m_899b0d31_5122_4616_b662_d79a2f207d1e_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V, G <= M -> HasPlanarDrawingOn M -> M <= G) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
      3 * Fintype.card V <= G.edgeFinset.card + 6) := by
  classical
  obtain ⟨ H, hGH, hH, hcount ⟩ :=
    WilliamsonShmoys.planar_drawing_completion_edge_count__p2m_899b0d31_5122_4616_b662_d79a2f207d1e_a1
      G hG hcard
  have hHG : H <= G := hmax H hGH hH
  have hEq : G = H := le_antisymm hGH hHG
  subst H
  exact Nat.le_of_eq hcount