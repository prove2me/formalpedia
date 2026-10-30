-- Prove2me | solution 1 for WilliamsonShmoys.planar_full_edge_supergraph_maximal_edge_count_20261028_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:00:18.81619+00:00
-- url     : https://prove2.me/submissions/ad869771-ee70-4060-9a3a-695f8c4c251f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_cbce8d52_767a_43cf_a345_07ed3485307d
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_cbce8d52_767a_43cf_a345_07ed3485307d

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨H, hKH, hHDraw, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph_cbce8d52_767a_43cf_a345_07ed3485307d
      K hDraw
  have hEq :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_cbce8d52_767a_43cf_a345_07ed3485307d
      H hV hHDraw hMax
  exact (Set.ncard_mono (SimpleGraph.edgeSet_mono hKH)).trans hEq.le