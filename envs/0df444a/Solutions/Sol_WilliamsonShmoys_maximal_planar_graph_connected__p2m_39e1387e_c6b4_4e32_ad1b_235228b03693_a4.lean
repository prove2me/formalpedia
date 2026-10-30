-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_connected__p2m_39e1387e_c6b4_4e32_ad1b_235228b03693_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:48:31.013285+00:00
-- url     : https://prove2.me/submissions/f907aca9-982e-4895-b401-fdb8471ec608
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_strict_extension_of_unreachable__p2m_8c53f87a_b244_43b9_9258_2c83805c4d13_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L)
    {u v : V} (huv : u ≠ v) :
    L.Reachable u v := by
  by_contra hUnreach
  obtain ⟨M, hLM, hM, hNotML⟩ := WilliamsonShmoys.planar_drawingOn_strict_extension_of_unreachable__p2m_8c53f87a_b244_43b9_9258_2c83805c4d13_a2 L hL huv hUnreach
  exact hNotML (hMax M hLM hM)