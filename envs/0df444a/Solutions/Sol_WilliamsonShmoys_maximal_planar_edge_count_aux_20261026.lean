-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_aux_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:24:23.744434+00:00
-- url     : https://prove2.me/submissions/e011314f-b780-4b37-849b-18692b10b80d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_repair_20261026
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_repair_20261026

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet →
      HasPlanarDrawingOn L →
      K.edgeSet = L.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper :=
    WilliamsonShmoys.planar_edge_upper_bound_repair_20261026 K hV hK
  have hlower :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound_repair_20261026
      K hV hK hmax
  omega