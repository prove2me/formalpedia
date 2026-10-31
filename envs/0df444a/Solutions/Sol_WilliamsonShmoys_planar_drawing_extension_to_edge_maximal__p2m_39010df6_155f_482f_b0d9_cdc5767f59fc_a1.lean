-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extension_to_edge_maximal__p2m_39010df6_155f_482f_b0d9_cdc5767f59fc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:55:38.554543+00:00
-- url     : https://prove2.me/submissions/3c901428-f23a-4637-83cb-200b335fcbf9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite__p2m_24784cbb_b8f6_4e91_b5ba_b51ad6a651ca_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hV : 3 ≤ Fintype.card V) :
    ∃ Y : SimpleGraph V, X ≤ Y ∧ WilliamsonShmoys.HasPlanarDrawingOn Y ∧
      ∀ Z : SimpleGraph V, Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Y = Z := by
  classical
  exact WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_24784cbb_b8f6_4e91_b5ba_b51ad6a651ca_a1
    (V := V) (P := WilliamsonShmoys.HasPlanarDrawingOn) X hX