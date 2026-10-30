-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_count__p2m_aad1f7a7_a04a_47ce_bdaf_91f7c06a5480_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:48:52.621176+00:00
-- url     : https://prove2.me/submissions/c4c5527b-0e19-49e5-898b-09f2d543e3ce

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count_7369a359

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    ∃ f : ℕ, Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      2 * M.edgeSet.ncard ≤ 3 * f := by
  obtain ⟨H, hMH, hHdraw, hEdges⟩ :=
    WilliamsonShmoys.maximal_planar_completion_edge_count_7369a359
      M hM hCard
  have hHM : H = M := hMax H hMH hHdraw
  subst H
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega