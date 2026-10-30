-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_4881293e_7bf5_4184_9f0b_57a8f75b0b6d
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:01:49.409041+00:00
-- url     : https://prove2.me/submissions/2ed39fac-30c3-4720-b368-8f0e46bd5018

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_4881293e_7bf5_4184_9f0b_57a8f75b0b6d

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    ∃ T : SimpleGraph V,
      L ≤ T ∧ T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hLT, hT, hMax⟩ :=
    WilliamsonShmoys.planar_extension_maximal_supergraph L hL hV
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_4881293e_7bf5_4184_9f0b_57a8f75b0b6d
      T hT hV hMax
  exact ⟨T, hLT, hCount⟩