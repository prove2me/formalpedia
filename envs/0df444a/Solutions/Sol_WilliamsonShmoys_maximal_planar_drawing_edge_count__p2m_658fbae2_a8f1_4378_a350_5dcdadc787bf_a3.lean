-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:29:33.202974+00:00
-- url     : https://prove2.me/submissions/5ef09fa1-668e-4b45-984e-9b44a534e78d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_b3857576_7612_4991_8128_4575dd8808dc_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  have hMaxEq : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
    intro N hMN hN
    exact le_antisymm (hMax N hMN hN) hMN
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition__p2m_b3857576_7612_4991_8128_4575dd8808dc_a1
      M hM hMaxEq hV
  omega