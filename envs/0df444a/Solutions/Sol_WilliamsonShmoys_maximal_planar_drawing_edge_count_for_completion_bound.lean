-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:54:37.695105+00:00
-- url     : https://prove2.me/submissions/953f7ab7-da69-41d0-bde6-4b2eb23d8709
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_ef555edc

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc K hV hK
  have hlower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_ef555edc
      K hV hK hmax
  omega