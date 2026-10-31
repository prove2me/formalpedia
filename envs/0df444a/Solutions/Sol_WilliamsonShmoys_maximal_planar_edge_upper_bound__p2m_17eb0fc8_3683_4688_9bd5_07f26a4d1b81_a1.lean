-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_17eb0fc8_3683_4688_9bd5_07f26a4d1b81_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:35:25.310979+00:00
-- url     : https://prove2.me/submissions/15694d4e-162e-4af9-b994-16453873f142
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_b9750e78_67e8_4f3e_9a0d_8a6e9da3267c_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * (Fintype.card V - 2) := by
  obtain ⟨H, _hKH, _hH, hcardMono, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_b9750e78_67e8_4f3e_9a0d_8a6e9da3267c_a1
      K hV hK
  calc
    K.edgeSet.ncard ≤ H.edgeSet.ncard := hcardMono
    _ = 3 * (Fintype.card V - 2) := hcard