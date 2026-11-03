-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_component_bridge__p2m_c8645d84_972c_4350_854f_f6f7bdb58b09_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:53:28.390946+00:00
-- url     : https://prove2.me/submissions/1933e5f2-5418-4348-bf26-f5950ea35b9a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_nonconnected_edge_attachment__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a5
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V)
    (hdis : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v := by
  obtain ⟨u, v, huv, hreach, H, hGH, hH, hadj⟩ :=
    WilliamsonShmoys.planar_nonconnected_edge_attachment__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a5 G hG hcard hdis
  refine ⟨H, hGH, hH, u, v, hreach, ?_⟩
  exact (hadj u v).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
