-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_simple_graph_has_edge_count_3n_minus_6_19818e22
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:07:17.653676+00:00
-- url     : https://prove2.me/submissions/153df7ed-5849-4206-a6e8-28f129f9e574
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet = K.edgeSet) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hLcount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulating_extension K hV hK
  have hsets : K.edgeSet = L.edgeSet := (hmax L hKL hL).symm
  rw [hsets]
  exact hLcount