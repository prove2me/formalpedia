-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_exists
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:49:00.21652+00:00
-- url     : https://prove2.me/submissions/aa7510fb-5b8e-4d2a-8dc6-2e19a49ba664

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_element_of_finite

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      H <= K /\
      WilliamsonShmoys.HasPlanarDrawingOn K /\
      forall L : SimpleGraph V,
        K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K := by
  classical
  obtain ⟨K, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_element_of_finite
      ({K : SimpleGraph V | H <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K})
      ⟨H, le_rfl, hH⟩
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  exact hmax L ⟨le_trans hK.1 hKL, hL⟩ hKL