-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_edge_bound__p2m_c6470163_a9cd_431f_b992_62a6706eed9c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:30:11.843085+00:00
-- url     : https://prove2.me/submissions/f8ccf344-553c-40db-94b6-3e12fc02113f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_8a1de5a7_e6e0_49bf_bc1c_04323822a27c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_8a1de5a7_e6e0_49bf_bc1c_04323822a27c_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ u v, L.Adj u v → M.Adj u v) ∧
      3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨M, hM, hLM, hmax⟩ := WilliamsonShmoys.planar_drawing_maximal_extension__p2m_8a1de5a7_e6e0_49bf_bc1c_04323822a27c_a1 L hL
  exact ⟨M, hM, hLM, WilliamsonShmoys.maximal_planar_edge_bound__p2m_8a1de5a7_e6e0_49bf_bc1c_04323822a27c_a1 M hM hmax hcard⟩