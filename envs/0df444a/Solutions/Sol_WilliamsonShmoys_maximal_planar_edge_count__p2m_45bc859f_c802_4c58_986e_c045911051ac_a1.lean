-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_45bc859f_c802_4c58_986e_c045911051ac_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:42:00.214498+00:00
-- url     : https://prove2.me/submissions/64d28051-9944-421b-aa2c-e7e16ca48217
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph__p2m_4536f73e_ef32_44ed_9a4a_358d0b7012c5_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hMax : forall K : SimpleGraph V, J <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = J)
    (hCard : 3 <= Fintype.card V) : J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hSub, hKDraw, hCount⟩ :=
    WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_4536f73e_ef32_44ed_9a4a_358d0b7012c5_a1 J hDraw hCard
  have hEq : K = J := hMax K hSub hKDraw
  simpa [hEq] using hCount