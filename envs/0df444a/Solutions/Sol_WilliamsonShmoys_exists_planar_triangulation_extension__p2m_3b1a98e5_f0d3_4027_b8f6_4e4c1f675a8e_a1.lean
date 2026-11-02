-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_extension__p2m_3b1a98e5_f0d3_4027_b8f6_4e4c1f675a8e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:05:14.036475+00:00
-- url     : https://prove2.me/submissions/13cc97c1-1e44-4246-9533-8fb6752c5f1a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_d8587c1f_e0c9_4a1c_96ac_f198f2c65871_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_d8587c1f_e0c9_4a1c_96ac_f198f2c65871_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ P : SimpleGraph V, N ≤ P ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ [DecidableRel P.Adj],
        P.edgeFinset.card + 6 = 3 * Fintype.card V := by
  obtain ⟨P, hNP, _hPconn, hPdraw, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension__p2m_d8587c1f_e0c9_4a1c_96ac_f198f2c65871_a1
      N hN hconn
  refine ⟨P, hNP, hPdraw, ?_⟩
  intro inst
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_d8587c1f_e0c9_4a1c_96ac_f198f2c65871_a1
    P hPdraw hmax hcard
