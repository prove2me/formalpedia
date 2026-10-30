-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_edge_count_acab26a7
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:32:12.782554+00:00
-- url     : https://prove2.me/submissions/0c17296a-9906-4ebd-a65b-5a022d4350b8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_maximal_extension_a305a22a
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_maximal_edge_count_a305a22a

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_maximal_extension_a305a22a H hH
  have hcount :=
    WilliamsonShmoys.planar_supergraph_triangulation_maximal_edge_count_a305a22a
      K hV hK hmax
  exact ⟨K, hHK, hK, hcount⟩