-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count_651e6155_repair2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:16:27.481027+00:00
-- url     : https://prove2.me/submissions/3b4f73b1-a8db-48ec-87f6-2e417d525397

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_b80c2ba3_repair2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax :
      ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N →
        M.edgeSet ⊆ N.edgeSet → N.edgeSet = M.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hN, hSub, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_b80c2ba3_repair2
      M hDrawing hCard
  have hEq : N.edgeSet = M.edgeSet := hmax N hN hSub
  simpa [hEq] using hCount