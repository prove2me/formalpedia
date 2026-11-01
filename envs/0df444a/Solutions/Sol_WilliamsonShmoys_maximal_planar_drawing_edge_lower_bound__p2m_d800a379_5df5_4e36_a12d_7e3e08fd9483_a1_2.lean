-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_d800a379_5df5_4e36_a12d_7e3e08fd9483_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:21:35.943781+00:00
-- url     : https://prove2.me/submissions/81cf013e-1d02-4323-b9e0-9677d2f26e27

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_repair_20261026

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeSet = L.edgeSet) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_edge_lower_bound_repair_20261026 K hV hK hmax
