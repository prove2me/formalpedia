-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_ef0860d4_4cfe_4ed1_9f37_9a24872db6ea_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:43:43.127493+00:00
-- url     : https://prove2.me/submissions/1e982043-7f45-4c38-a4b5-4885e010c5f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_bc657f31_eaae_4f57_ab42_14b02319f13d_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation__p2m_bc657f31_eaae_4f57_ab42_14b02319f13d_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ W : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn W → U ≤ W → W ≤ U) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_bc657f31_eaae_4f57_ab42_14b02319f13d_a1 U hU hCard
  by_contra hneq
  have hlt : U.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨W, hW, hUW⟩ := WilliamsonShmoys.planar_edge_augmentation__p2m_bc657f31_eaae_4f57_ab42_14b02319f13d_a1 U hU hCard hlt
  have hback : W ≤ U := hmax W hW (le_of_lt hUW)
  exact (not_le_of_gt hUW) hback