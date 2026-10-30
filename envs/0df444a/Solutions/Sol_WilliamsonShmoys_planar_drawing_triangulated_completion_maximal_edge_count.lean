-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulated_completion_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:15:32.651198+00:00
-- url     : https://prove2.me/submissions/a8ef2c59-abcf-46df-bc5c-e30f0267c248

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulated_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMaximal : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (n : Nat)
    (hLarge : 3 ≤ n)
    (hcard : Fintype.card V = n) :
    K.edgeSet.ncard = 3 * n - 6 := by
  obtain ⟨L, hKL, hLDrawing, hLcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulated_completion
      K hDrawing n hLarge hcard
  have hLK : L ≤ K := hMaximal L hKL hLDrawing
  have hEq : L = K := le_antisymm hLK hKL
  rw [← hEq]
  exact hLcount