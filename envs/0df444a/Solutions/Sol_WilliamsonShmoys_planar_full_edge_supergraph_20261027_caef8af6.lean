-- Prove2me | solution 1 for WilliamsonShmoys.planar_full_edge_supergraph_20261027_caef8af6
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:36:08.44601+00:00
-- url     : https://prove2.me/submissions/85bf4cad-0577-4640-b95e-ef23f373cb14

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_full_edge_supergraph_maximal_extension_20261028
import Theorems.Thm_WilliamsonShmoys_planar_full_edge_supergraph_maximal_edge_count_20261028

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hsub, hKdraw, hmax⟩ :=
    WilliamsonShmoys.planar_full_edge_supergraph_maximal_extension_20261028 H hV hDraw
  refine ⟨K, hsub, hKdraw, ?_⟩
  exact WilliamsonShmoys.planar_full_edge_supergraph_maximal_edge_count_20261028 K hV hKdraw hmax