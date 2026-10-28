-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:10:18.794157+00:00
-- url     : https://prove2.me/submissions/a5ea95a5-3ed0-4e34-8253-920c8b1e2f0c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_triangulation_extension

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hYdraw : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hMax : ∀ Z : SimpleGraph V, Y ≤ Z →
      WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y) :
    3 * Fintype.card V = Y.edgeSet.ncard + 6 := by
  obtain ⟨Z, hYZ, hZdraw, hCount⟩ :=
    WilliamsonShmoys.exists_drawable_triangulation_extension Y hCard hYdraw
  have hZY : Z = Y := hMax Z hYZ hZdraw
  subst Z
  omega