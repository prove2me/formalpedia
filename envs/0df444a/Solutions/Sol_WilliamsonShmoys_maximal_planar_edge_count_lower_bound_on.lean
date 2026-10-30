-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_on
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T21:04:23.824767+00:00
-- url     : https://prove2.me/submissions/4f2b4248-8c7a-4f04-ae10-2b607a8502a3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_IsMaximalPlanarOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_triangulation_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHmax : WilliamsonShmoys.IsMaximalPlanarOn H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hKdrawing, hKcount⟩ :=
    WilliamsonShmoys.planar_drawing_on_triangulation_extension H hHmax.1 hV
  have hKH : K = H := hHmax.2 K hHK hKdrawing
  rw [← hKH]
  omega