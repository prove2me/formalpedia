-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension_exists__p2m_efe3e864_4fbd_4f0b_a1f2_70ba02623cb8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:22:09.905973+00:00
-- url     : https://prove2.me/submissions/085031f0-d9de-4119-a245-8e00b3516960

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_max_edge_card__p2m_c5685e49_0d83_46bc_bcc2_05a6dc60419f_a2
import Theorems.Thm_WilliamsonShmoys_simpleGraph_eq_of_edge_card_le__p2m_c5685e49_0d83_46bc_bcc2_05a6dc60419f_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by
  classical
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_max_edge_card__p2m_c5685e49_0d83_46bc_bcc2_05a6dc60419f_a2
      N hN
  refine ⟨K, hNK, hK, ?_⟩
  intro L hKL hL
  exact WilliamsonShmoys.simpleGraph_eq_of_edge_card_le__p2m_c5685e49_0d83_46bc_bcc2_05a6dc60419f_a2
    K L hKL (hmax L (le_trans hNK hKL) hL)