-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_lower_bound_e51c1790
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:07:26.359154+00:00
-- url     : https://prove2.me/submissions/20c4e22e-faa5-4ea5-a11d-6dd30f097b7a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_augmentation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V,
      U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = U) :
    3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by
  by_contra hnot
  have hdeficit : U.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨W, hUW, hWne, hW⟩ :=
    WilliamsonShmoys.planar_graph_edge_augmentation U hV hU hdeficit
  exact hWne (hmax W hUW hW)