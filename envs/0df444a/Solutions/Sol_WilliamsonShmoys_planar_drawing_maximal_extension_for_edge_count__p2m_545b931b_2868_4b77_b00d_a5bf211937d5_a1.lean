-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count__p2m_545b931b_2868_4b77_b00d_a5bf211937d5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:46:27.47329+00:00
-- url     : https://prove2.me/submissions/fed15a76-d271-4cca-bf6f-62088384bd11
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_property_extension_maximal__p2m_af21b660_e263_41f3_a209_fea21d5ace1b_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V,
      K.edgeSet ⊆ M.edgeSet ∧
      K.edgeSet.ncard ≤ M.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M.edgeSet ⊆ N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet ⊆ M.edgeSet := by
  obtain ⟨M, hKM, hM, hmax⟩ :=
    WilliamsonShmoys.finite_property_extension_maximal__p2m_af21b660_e263_41f3_a209_fea21d5ace1b_a1
      K WilliamsonShmoys.HasPlanarDrawingOn hK
  refine ⟨M, hKM, Set.ncard_mono hKM, hM, ?_⟩
  intro N hMN hN
  exact hmax N hMN hN