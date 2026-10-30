-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_with_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:59:41.484007+00:00
-- url     : https://prove2.me/submissions/9b2b7f5c-99c8-4382-b597-d02459c7ee36

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_maximal_aux_20261026
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_aux_20261026

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      Set.Subset H.edgeSet K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_extension_maximal_aux_20261026 H hH
  have hcount := WilliamsonShmoys.maximal_planar_edge_count_aux_20261026 K hV hK hmax
  exact ⟨K, hHK, hK, hcount⟩
