-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7ce99e29_e187_4d62_b312_8a5637649ce2_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:07:04.580429+00:00
-- url     : https://prove2.me/submissions/70eadbd0-a64f-483c-9b82-30a73c44a95c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by
  cases WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count
      H hV hplanar with
  | intro K hK =>
    cases hK with
    | intro hHK hRest =>
      cases hRest with
      | intro hKplanar hCount =>
        have hKH : K = H := hmax K hHK hKplanar
        rw [hKH] at hCount
        omega