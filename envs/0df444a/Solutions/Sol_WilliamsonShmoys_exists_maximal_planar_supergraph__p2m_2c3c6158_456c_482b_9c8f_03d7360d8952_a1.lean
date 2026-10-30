-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_2c3c6158_456c_482b_9c8f_03d7360d8952_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:57:59.310496+00:00
-- url     : https://prove2.me/submissions/9ebeb857-cd03-4aee-8e0a-99852bfe7724
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_partial_order_has_maximal_element__p2m_cebdf6a5_ed21_4e3f_9527_133aad01d215_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by
  classical
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  obtain ⟨K, hK, hmax⟩ :=
    finite_partial_order_has_maximal_element__p2m_cebdf6a5_ed21_4e3f_9527_133aad01d215_a1
      (P := fun K : SimpleGraph V => N ≤ K ∧ HasPlanarDrawingOn K)
      ⟨N, le_rfl, hN⟩
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  exact hmax L ⟨hK.1.trans hKL, hL⟩ hKL