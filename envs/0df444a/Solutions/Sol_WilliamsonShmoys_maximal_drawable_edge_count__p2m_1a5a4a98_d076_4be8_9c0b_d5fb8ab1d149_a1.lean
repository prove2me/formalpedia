-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_1a5a4a98_d076_4be8_9c0b_d5fb8ab1d149_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:32:18.955529+00:00
-- url     : https://prove2.me/submissions/170eaeef-71b5-433e-9bd7-1444b1b9ae82

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_triangulated_extension__p2m_646b5b89_5112_4cc7_9d4e_a59724ef3107_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ P : SimpleGraph V,
      N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨P, hNP, hDrawP, hCount⟩ :=
    WilliamsonShmoys.drawable_triangulated_extension__p2m_646b5b89_5112_4cc7_9d4e_a59724ef3107_a1
      N hDraw hCard
  have hEq : P = N := hMax P hNP hDrawP
  simpa [hEq] using hCount