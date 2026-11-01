-- Prove2me | solution 1 for WilliamsonShmoys.drawable_triangulation_extension_edge_count__p2m_cd754a9f_7b3b_4f66_b68b_c9f75eba4801_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:37:36.655333+00:00
-- url     : https://prove2.me/submissions/340017f6-3fdc-498d-a7b6-62c98f24cb18
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_drawable_planar_supergraph_maximal__p2m_5303ee26_08e8_4d11_9742_cd82622b8993_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_lower_bound__p2m_5303ee26_08e8_4d11_9742_cd82622b8993_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (N : SimpleGraph V), M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∃ (dN : DecidableRel N.Adj),
        (letI : DecidableRel N.Adj := dN
         3 * Fintype.card V - 6 ≤ N.edgeFinset.card) := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.drawable_planar_supergraph_maximal__p2m_5303ee26_08e8_4d11_9742_cd82622b8993_a1
      M hM hcard
  obtain ⟨dN, hbound⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_edge_lower_bound__p2m_5303ee26_08e8_4d11_9742_cd82622b8993_a1
      N hN hcard hmax
  exact ⟨N, hMN, hN, dN, hbound⟩