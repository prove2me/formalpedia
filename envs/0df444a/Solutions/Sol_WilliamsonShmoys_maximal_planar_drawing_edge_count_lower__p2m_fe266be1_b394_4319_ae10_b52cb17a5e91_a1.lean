-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_fe266be1_b394_4319_ae10_b52cb17a5e91_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:45:42.606328+00:00
-- url     : https://prove2.me/submissions/8f2d9627-a42b-4560-aa2a-45ee55de520e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_maximal_edge_count__p2m_d65752b0_c280_4c98_926b_0ae69c395723_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall K : SimpleGraph V,
      M <= K -> HasPlanarDrawingOn K -> K = M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  have hExt :=
    planar_supergraph_with_maximal_edge_count__p2m_d65752b0_c280_4c98_926b_0ae69c395723_a1
      M hM hCard
  cases hExt with
  | intro K hExt =>
    cases hExt with
    | intro hMK hExt =>
      cases hExt with
      | intro hK hEdges =>
        have hKM : K = M := hMax K hMK hK
        have hEdgesM : M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
          simpa [hKM] using hEdges
        omega