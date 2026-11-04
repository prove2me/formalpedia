-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_d7b584f5_f48a_4e68_a764_d92a7993a6d3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:09:41.106872+00:00
-- url     : https://prove2.me/submissions/26b13a63-1050-40d8-8f84-140d63aa860e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_triangulate_planar_graph__p2m_0abcdb56_bfcd_4329_9382_36e3242f584a_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    3 * Fintype.card V ≤ L.edgeFinset.card + 6 := by
  classical
  obtain ⟨T, hLT, hTdraw, hTcard⟩ :=
    WilliamsonShmoys.triangulate_planar_graph__p2m_0abcdb56_bfcd_4329_9382_36e3242f584a_a1
      L hV hL
  have hEq : T = L := hmax T hLT hTdraw
  rw [hEq] at hTcard
  exact Nat.le_of_eq hTcard