-- Prove2me | solution 2 for WilliamsonShmoys.edge_maximal_planar_supergraph__p2m_aea893ff_524d_432f_a94f_a28f6a185e5e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:23:57.094649+00:00
-- url     : https://prove2.me/submissions/79dad4f1-caeb-4a1b-8529-e72e33d66baf

import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_finite_maximal_extension

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) : ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K :=
  WilliamsonShmoys.exists_planar_supergraph_finite_maximal_extension G hG hCard
