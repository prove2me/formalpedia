-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_94636b31_2f9e_4256_93d0_7a9950cdcd71_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:46:16.099473+00:00
-- url     : https://prove2.me/submissions/3a919396-9136-4555-8922-176c55131bd3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_has_maximal_element__p2m_21abd8cf_71a5_4301_9a22_948ffb9f2078_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ (L : SimpleGraph V) [DecidableRel L.Adj],
        HasPlanarDrawingOn L → K ≤ L → L ≤ K := by
  obtain ⟨K, hK, hmax⟩ :=
    WilliamsonShmoys.finite_simpleGraph_has_maximal_element__p2m_21abd8cf_71a5_4301_9a22_948ffb9f2078_a1
      (P := fun K : SimpleGraph V => H ≤ K ∧ HasPlanarDrawingOn K)
      ⟨H, le_rfl, hH⟩
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L inst hL hKL
  exact hmax L ⟨le_trans hK.1 hKL, hL⟩ hKL