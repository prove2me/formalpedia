-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_707fd91e
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:04:11.613781+00:00
-- url     : https://prove2.me/submissions/86a80747-62e8-4b06-be16-8c1be618f000

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_edge_bound_93cad1d3_6631_4871_91db_d5199271705a

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hbound⟩ :=
    WilliamsonShmoys.planar_drawing_augmentation_edge_bound_93cad1d3_6631_4871_91db_d5199271705a
      K hV hK
  have hLK : L = K := hmax L hKL hL
  simpa [hLK] using hbound