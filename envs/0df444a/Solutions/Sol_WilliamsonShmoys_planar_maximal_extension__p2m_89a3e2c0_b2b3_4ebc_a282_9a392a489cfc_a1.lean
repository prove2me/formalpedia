-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_89a3e2c0_b2b3_4ebc_a282_9a392a489cfc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:58:19.034263+00:00
-- url     : https://prove2.me/submissions/268b124b-81a2-44d4-ad10-7e387c15875b

import Mathlib
import Theorems.Thm_finite_preorder_has_maximal__p2m_d50bd5f9_430a_4ac6_90e0_7716421734c3_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by
  classical
  let P : SimpleGraph V → Prop := fun K => H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  have hP : ∃ K, P K := ⟨H, le_rfl, hH⟩
  obtain ⟨K, hK, hmax⟩ :=
    finite_preorder_has_maximal__p2m_d50bd5f9_430a_4ac6_90e0_7716421734c3_a1 P hP
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  exact hmax L ⟨le_trans hK.1 hKL, hL⟩ hKL