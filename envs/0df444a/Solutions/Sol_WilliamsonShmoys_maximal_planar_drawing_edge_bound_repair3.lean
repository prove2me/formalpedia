-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound_repair3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:35:55.376733+00:00
-- url     : https://prove2.me/submissions/b50ebf76-408b-485a-b9da-522e2c8961ca

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_repair3

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hM, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_repair3 L hL hCard
  have hEq : M = L := hMax M hLM hM
  rw [← hEq]
  omega