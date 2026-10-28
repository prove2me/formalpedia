-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound_for_triangulation_1e14dc85_fe67_4e30_934e_c619828dd605
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:57:34.43693+00:00
-- url     : https://prove2.me/submissions/ddc8042d-ddc3-41b0-bd19-489ba2a1931b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_supergraph_d41641eb_86db_4b4e_b9d1_2259e7f78f1b

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDrawing : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMaximal : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hNdraw, hTriangulated⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulation_supergraph_d41641eb_86db_4b4e_b9d1_2259e7f78f1b
      M hDrawing hCard
  have hNM : N ≤ M := hMaximal N hMN hNdraw
  have hEq : N = M := le_antisymm hNM hMN
  rw [← hEq]
  exact hTriangulated