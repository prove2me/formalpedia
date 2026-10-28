-- Prove2me | solution 1 for WilliamsonShmoys.inclusion_maximal_planar_has_extremal_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:50:26.907345+00:00
-- url     : https://prove2.me/submissions/487ec5f3-feaa-455a-ab82-bae984d64d81
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_to_triangulation_edge_count
import Theorems.Thm_WilliamsonShmoys_edge_count_eq_of_mutually_le

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_augmentation_to_triangulation_edge_count K hV hK
  calc
    K.edgeSet.ncard = L.edgeSet.ncard :=
      WilliamsonShmoys.edge_count_eq_of_mutually_le K L hKL (hmax L hKL hL)
    _ = 3 * Fintype.card V - 6 := hcount