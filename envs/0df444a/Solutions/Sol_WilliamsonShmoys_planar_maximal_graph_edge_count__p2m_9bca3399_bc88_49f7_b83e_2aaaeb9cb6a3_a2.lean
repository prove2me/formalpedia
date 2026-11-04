-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_graph_edge_count__p2m_9bca3399_bc88_49f7_b83e_2aaaeb9cb6a3_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:06:13.810103+00:00
-- url     : https://prove2.me/submissions/96a4185f-58ad-404f-bab3-839f24907baa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_8f423fe5_b3be_4138_81a9_17669ac64a5c_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V)
    (hmax : forall (M : SimpleGraph V) [DecidableRel M.Adj],
      HasPlanarDrawingOn M ->
      G.edgeFinset ⊆ M.edgeFinset ->
      M.edgeFinset ⊆ G.edgeFinset) :
    G.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨H, instH, hsub, hH, hcard⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_8f423fe5_b3be_4138_81a9_17669ac64a5c_a2
      G hG hV
  letI : DecidableRel H.Adj := instH
  have hrev := hmax H hH hsub
  have heq : G.edgeFinset = H.edgeFinset := by
    apply Finset.ext
    intro e
    exact ⟨fun he => hsub he, fun he => hrev he⟩
  calc
    G.edgeFinset.card = H.edgeFinset.card := congrArg Finset.card heq
    _ = 3 * Fintype.card V - 6 := hcard