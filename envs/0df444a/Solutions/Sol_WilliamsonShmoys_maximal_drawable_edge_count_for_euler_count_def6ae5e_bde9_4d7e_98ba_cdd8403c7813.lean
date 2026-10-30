-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_for_euler_count_def6ae5e_bde9_4d7e_98ba_cdd8403c7813
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:23:05.738124+00:00
-- url     : https://prove2.me/submissions/7eab246b-a9c0-4688-977c-3443517a6c4f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLDrawing, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion_edge_count_v2 K hK hCard
  have hLK : L <= K := hMax L hKL hLDrawing
  have hEq : L = K := le_antisymm hLK hKL
  simpa [hEq] using hCount