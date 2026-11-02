-- Prove2me | solution 1 for WilliamsonShmoys.connected_induced_planar_edge_bound__p2m_ac18a95b_13f8_4a76_980e_021bef74dbe9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:41:31.947137+00:00
-- url     : https://prove2.me/submissions/4d77aa67-36f2-49cc-b3c0-18070e7a03f5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_restrict_planar_drawing_to_induced_subgraph__p2m_ed6487b5_3fd2_47fb_a969_c3848ac24208_a1
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound__p2m_ed6487b5_3fd2_47fb_a969_c3848ac24208_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∀ s : Finset V, 3 <= s.card →
      (N.induce (s : Set V)).Connected →
      (N.induce (s : Set V)).edgeFinset.card <= 3 * s.card - 6 := by
  letI : DecidableRel N.Adj := dN
  intro s hs hconn
  have hDraw : WilliamsonShmoys.HasPlanarDrawingOn (N.induce (s : Set V)) :=
    WilliamsonShmoys.restrict_planar_drawing_to_induced_subgraph__p2m_ed6487b5_3fd2_47fb_a969_c3848ac24208_a1
      N hN s
  have hCard : 3 <= Fintype.card {x // x ∈ s} := by
    simpa using hs
  have hBound :=
    WilliamsonShmoys.planar_connected_edge_bound__p2m_ed6487b5_3fd2_47fb_a969_c3848ac24208_a1
      (N.induce (s : Set V)) hDraw hconn hCard
  simpa using hBound