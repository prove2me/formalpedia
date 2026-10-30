-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_maximal_connected__p2m_84aa0f8d_42a4_4615_a166_b73b4ced676a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:02:28.562986+00:00
-- url     : https://prove2.me/submissions/3bb54d93-207b-4860-b2da-a0bedadee7e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_planar_extension__p2m_8a5c6ab3_e805_464b_b048_a38e7a7d5336_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H)
    (hmax : ∀ G : SimpleGraph V, H ≤ G → HasPlanarDrawingOn G → G ≤ H) :
    H.Connected := by
  classical
  by_contra hconn
  obtain ⟨G, hHG, hGplanar, hnotGH⟩ :=
    WilliamsonShmoys.planar_disconnected_has_planar_extension__p2m_8a5c6ab3_e805_464b_b048_a38e7a7d5336_a2
      H hV hH hconn
  exact hnotGH (hmax G hHG hGplanar)