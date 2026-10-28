-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count_eb48bd77
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:24:55.432374+00:00
-- url     : https://prove2.me/submissions/104fa01b-ec8d-4d98-abcc-3dee64fe48c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_exact_count
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_eq

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L.edgeSet ⊂ M.edgeSet → ¬ HasPlanarDrawingOn M) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hLK, hKDraw, hKCount⟩ :=
    WilliamsonShmoys.planar_drawing_completion_exact_count L hDraw hCard
  have hEq := WilliamsonShmoys.maximal_drawable_supergraph_eq L K hDraw hMax hLK hKDraw
  simpa [hEq] using hKCount