-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound_47cfe247_f32d_4afb_b363_54161b3a97c2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:09:24.546732+00:00
-- url     : https://prove2.me/submissions/d90dadbf-a5da-4ddc-87a2-7fd16c25d3c7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_dense_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall P : SimpleGraph V, N <= P ->
      WilliamsonShmoys.HasPlanarDrawingOn P -> P = N) :
    3 * Fintype.card V - 6 <= N.edgeSet.ncard := by
  obtain ⟨P, hNP, hP, hbound⟩ :=
    WilliamsonShmoys.planar_graph_has_dense_extension N hV hN
  have hPN : P = N := hmax P hNP hP
  simpa [hPN] using hbound