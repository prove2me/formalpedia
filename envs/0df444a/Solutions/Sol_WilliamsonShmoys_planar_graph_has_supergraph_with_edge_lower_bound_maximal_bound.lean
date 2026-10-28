-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_supergraph_with_edge_lower_bound_maximal_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:20:09.901584+00:00
-- url     : https://prove2.me/submissions/71c3140f-ab4c-4bff-9705-3dd147b41a23
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hMax : ∀ W : SimpleGraph V,
      Z ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ Z) :
    3 * Fintype.card V ≤ Z.edgeSet.ncard + 6 := by
  by_contra hbound
  have hsmall : Z.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨W, hZW, hW⟩ :=
    WilliamsonShmoys.planar_drawing_edge_augmentation
      (V := V) (Z := Z) hV hZ hsmall
  have hle : W ≤ Z := hMax W (le_of_lt hZW) hW
  exact (not_le_of_gt hZW) hle