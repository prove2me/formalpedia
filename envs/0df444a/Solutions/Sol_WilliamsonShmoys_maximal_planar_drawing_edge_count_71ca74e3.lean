-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_71ca74e3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:28:50.53362+00:00
-- url     : https://prove2.me/submissions/46096a69-474a-46c3-96fa-200f71c6289a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_9525bc2d_6e0d_4029_99f4_e9901dcdc86f

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ X : SimpleGraph V,
      LE.le W X → WilliamsonShmoys.HasPlanarDrawingOn X → LE.le X W)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 = W.edgeSet.ncard := by
  obtain ⟨X, hWX, hX, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_9525bc2d_6e0d_4029_99f4_e9901dcdc86f W hW hV
  have hXW : LE.le X W := hmax X hWX hX
  have hEq : W = X := le_antisymm hWX hXW
  calc
    3 * Fintype.card V - 6 = X.edgeSet.ncard := hcount.symm
    _ = W.edgeSet.ncard := by rw [← hEq]