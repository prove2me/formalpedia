-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_drawable_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:11:08.770215+00:00
-- url     : https://prove2.me/submissions/e49d606b-674e-4a45-92b2-eb4ba519f4e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_3d83e52d_d7f3_4064_9901_f4d565126921
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_3d83e52d_d7f3_4064_9901_f4d565126921
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    Exists fun X : SimpleGraph V => W <= X /\ 
      WilliamsonShmoys.HasPlanarDrawingOn X /\
      3 * Fintype.card V = X.edgeSet.ncard + 6 := by
  obtain ⟨X, hWX, hX, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_3d83e52d_d7f3_4064_9901_f4d565126921 W hW
  exact ⟨X, hWX, hX,
    WilliamsonShmoys.maximal_drawable_edge_count_3d83e52d_d7f3_4064_9901_f4d565126921 X hV hX hmax⟩