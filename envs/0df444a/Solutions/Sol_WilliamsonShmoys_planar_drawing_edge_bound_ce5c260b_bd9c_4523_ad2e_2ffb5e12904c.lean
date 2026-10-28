-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_ce5c260b_bd9c_4523_ad2e_2ffb5e12904c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:45:47.418738+00:00
-- url     : https://prove2.me/submissions/14ab4b23-8b26-4cba-972e-0ac544192555
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph_for_edge_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_equations_for_edge_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V) :
    N.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨M, hNM, hM, hMax, hEdges⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_for_edge_bound N hN
  obtain ⟨f, hEuler, hTriangular⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_face_equations_for_edge_bound
      M hM hMax hCard
  have hMaxBound : M.edgeSet.ncard + 6 = 3 * Fintype.card V := by omega
  omega