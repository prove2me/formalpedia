-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_08c24848_031b_43ea_aa26_092fb49494c8_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:46:00.66754+00:00
-- url     : https://prove2.me/submissions/a0426579-7c62-45bd-a1b9-5e4b1550cde0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_augmentation__p2m_ef7f67a4_b20c_4576_8674_97edcb1c6ef4_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M <= N -> HasPlanarDrawingOn N -> N = M) :
    (letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
     3 * Fintype.card V - 6 <= M.edgeFinset.card) := by
  classical
  obtain ⟨H, hsub, hH, hHcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_augmentation__p2m_ef7f67a4_b20c_4576_8674_97edcb1c6ef4_a1
      M hcard hM
  have hHM : H = M := hmax H hsub hH
  rw [← hHM]
  omega