-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_e6187372_db43_4b05_9178_6f8ead22bdbc
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:56:23.299435+00:00
-- url     : https://prove2.me/submissions/6da2a58f-b064-4fb7-8844-b095ace8059e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_drawing_has_triangulation_extension
set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hK, hCount⟩ :=
    WilliamsonShmoys.finite_planar_drawing_has_triangulation_extension N hV hN
  have hKN : K = N := hMax K hNK hK
  rw [hKN] at hCount
  exact hCount