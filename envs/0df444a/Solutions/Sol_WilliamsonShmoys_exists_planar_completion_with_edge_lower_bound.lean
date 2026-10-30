-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_completion_with_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:15:44.436993+00:00
-- url     : https://prove2.me/submissions/d1d9f77a-d73a-430b-9743-5396ef03d879

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion_3655d1b6_6c4a_40a3_8c82_ff009c818c61
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_3655d1b6_6c4a_40a3_8c82_ff009c818c61

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H <= K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hKdraw, hKmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_completion_3655d1b6_6c4a_40a3_8c82_ff009c818c61 H hV hH
  exact ⟨K, hHK, hKdraw,
    WilliamsonShmoys.maximal_planar_edge_lower_bound_3655d1b6_6c4a_40a3_8c82_ff009c818c61 K hV hKdraw hKmax⟩