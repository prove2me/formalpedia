-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_ncard_triangulation_job9e56ac28_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T04:04:30.578991+00:00
-- url     : https://prove2.me/submissions/320c72ab-e1b2-4202-853e-c5f449abf9b8

import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_count_upper_bound__p2m_4e1da140_2dc1_48aa_a5de_903746e6acda_a7
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_4e1da140_2dc1_48aa_a5de_903746e6acda_a7

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hLmax : forall M : SimpleGraph V,
      L.edgeSet <= M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      M.edgeSet <= L.edgeSet) :
    3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  have hupper : L.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
    WilliamsonShmoys.planar_simple_edge_count_upper_bound__p2m_4e1da140_2dc1_48aa_a5de_903746e6acda_a7 L hV hLplanar
  have hlower : 3 * Fintype.card V <= L.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_4e1da140_2dc1_48aa_a5de_903746e6acda_a7 L hV hLplanar hLmax
  exact Nat.le_antisymm hlower hupper