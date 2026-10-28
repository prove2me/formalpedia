-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_subset_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T22:42:28.014839+00:00
-- url     : https://prove2.me/submissions/333ec7db-6449-463d-923e-fc2ffe8ebbe7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_induce_subset
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulation

set_option autoImplicit false

open scoped BigOperators

/-- The stated triangulation theorem follows by restricting the drawing to the selected vertices and applying the finite-set triangulation theorem. -/
theorem solution
    {n : Nat} (G : SimpleGraph (Fin n))
    (hG : WilliamsonShmoys.HasPlanarDrawing G)
    (S : Set (Fin n)) [Fintype S] (hS : 3 ≤ Fintype.card S) :
    ∃ (H : SimpleGraph S), G.induce S ≤ H ∧
      ∃ (m : Nat) (M : WilliamsonShmoys.TriangularMap H (Fin m)),
        2 * Fintype.card S = m + 4 := by
  obtain ⟨H, hsub, m, M, hm⟩ :=
    WilliamsonShmoys.planar_drawingOn_triangulation
      (G.induce S)
      (WilliamsonShmoys.planar_drawing_induce_subset G hG S)
      hS
  exact ⟨H, hsub, m, M, hm⟩