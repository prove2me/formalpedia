-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:07:26.706626+00:00
-- url     : https://prove2.me/submissions/dba863b7-85c6-44a2-b7f9-afe7cb0bc832

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph K hK
  refine ⟨H, hKH, hH, ?_⟩
  exact WilliamsonShmoys.maximal_drawing_edge_count H hH hV hmax