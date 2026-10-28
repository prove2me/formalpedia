-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:56:57.101992+00:00
-- url     : https://prove2.me/submissions/39eaf75d-a461-4c30-9a76-ebe207cfd3b3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_property_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) :
    ∃ L : SimpleGraph V, M ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ K : SimpleGraph V, L ≤ K → HasPlanarDrawingOn K → K = L := by
  exact WilliamsonShmoys.exists_maximal_property_extension M
    WilliamsonShmoys.HasPlanarDrawingOn hM