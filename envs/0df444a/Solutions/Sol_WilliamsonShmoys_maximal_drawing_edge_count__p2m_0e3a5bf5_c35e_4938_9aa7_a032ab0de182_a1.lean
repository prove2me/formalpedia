-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_edge_count__p2m_0e3a5bf5_c35e_4938_9aa7_a032ab0de182_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:31:42.428239+00:00
-- url     : https://prove2.me/submissions/226907fd-1d1d-4659-83b1-b12f760a00d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulated_extension__p2m_30f04ba5_7c4d_43f6_bbf4_fbaceb7763c4_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hDrawM, hCount⟩ :=
    WilliamsonShmoys.planar_triangulated_extension__p2m_30f04ba5_7c4d_43f6_bbf4_fbaceb7763c4_a1
      L hDraw hCard
  have hML : M ≤ L := hMax M hLM hDrawM
  have hEq : M = L := le_antisymm hML hLM
  simpa [hEq] using hCount