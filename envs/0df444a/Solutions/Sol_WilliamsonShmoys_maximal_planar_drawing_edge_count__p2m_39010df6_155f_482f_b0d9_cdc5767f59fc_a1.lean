-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_39010df6_155f_482f_b0d9_cdc5767f59fc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:59:58.517167+00:00
-- url     : https://prove2.me/submissions/c404d3d5-2e70-468a-868d-acf5dde7cf8a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_supergraph__p2m_e59a889d_669c_414e_8ddd_df780e6fdba8_a2
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ Z : SimpleGraph V, Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Y = Z) :
    Y.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨Z, hYZ, hZplanar, hZcount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulating_supergraph__p2m_e59a889d_669c_414e_8ddd_df780e6fdba8_a2 Y hY hV
  have hEq : Y = Z := hMax Z hYZ hZplanar
  rw [hEq]
  exact hZcount