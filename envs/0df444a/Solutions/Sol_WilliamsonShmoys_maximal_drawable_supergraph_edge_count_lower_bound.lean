-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_edge_count_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:51:38.487907+00:00
-- url     : https://prove2.me/submissions/32b2148e-9737-4ecd-ad38-39379623c2c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_drawable_supergraph
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ X : SimpleGraph V, W ≤ X →
      WilliamsonShmoys.HasPlanarDrawingOn X → X = W) :
    3 * Fintype.card V ≤ W.edgeSet.ncard + 6 := by
  obtain ⟨X, hWX, hX, htri⟩ :=
    WilliamsonShmoys.exists_triangulated_drawable_supergraph W hV hW
  have hEq : X = W := hmax X hWX hX
  rw [← hEq]
  omega