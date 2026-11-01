-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_72c268f3_7cc5_487f_ad8b_d5f36984db50_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:24:54.891887+00:00
-- url     : https://prove2.me/submissions/eab1b6e2-041d-4bba-8649-4d9dd6ebaccc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_bound__p2m_c6470163_a9cd_431f_b992_62a6706eed9c_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M →
      (∀ u v, L.Adj u v → M.Adj u v) →
      ∀ u v, M.Adj u v → L.Adj u v)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨M, hM, hLM, hbound⟩ :=
    WilliamsonShmoys.planar_drawing_completion_edge_bound__p2m_c6470163_a9cd_431f_b992_62a6706eed9c_a1
      L hL hcard
  have hML : M = L := by
    ext u v
    exact ⟨hmax M hM hLM u v, hLM u v⟩
  simpa [hML] using hbound