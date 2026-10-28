-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_augmentation_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:55:56.279999+00:00
-- url     : https://prove2.me/submissions/cd16b83b-e30c-4728-a4ac-ccb0af90d541
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_card_maximal_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_card_maximal_edge_count

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_card_maximal_planar_supergraph K hK
  have hmaxL : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet.ncard ≤ L.edgeSet.ncard := by
    intro M hLM hM
    exact hmax M (le_trans hKL hLM) hM
  have hcount :=
    WilliamsonShmoys.planar_supergraph_card_maximal_edge_count L hV hL hmaxL
  exact ⟨L, hKL, hL, hcount⟩