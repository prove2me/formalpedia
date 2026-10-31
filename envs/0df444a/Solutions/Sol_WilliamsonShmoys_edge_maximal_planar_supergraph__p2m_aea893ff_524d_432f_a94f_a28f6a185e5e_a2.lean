-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_supergraph__p2m_aea893ff_524d_432f_a94f_a28f6a185e5e_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:52:23.064518+00:00
-- url     : https://prove2.me/submissions/9a329403-5cd7-4ba8-bfe0-e0500853c72b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_card_maximal_drawable_extension__p2m_2c13f176_83f3_43cd_bbd0_841f438f66be_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_card_le_implies_eq__p2m_2c13f176_83f3_43cd_bbd0_841f438f66be_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_edge_card_maximal_drawable_extension__p2m_2c13f176_83f3_43cd_bbd0_841f438f66be_a1
      G hCard hG
  refine ⟨K, hGK, hK, ?_⟩
  intro L hKL hL
  exact WilliamsonShmoys.planar_edge_card_le_implies_eq__p2m_2c13f176_83f3_43cd_bbd0_841f438f66be_a1
    K L hKL (hmax L hKL hL)
