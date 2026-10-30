-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_0af2d81e_eda4_4f18_8ca2_a158577f115d_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:21:24.55647+00:00
-- url     : https://prove2.me/submissions/c24267e5-4e23-480f-9a9c-170684076d01
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_33fe1755_151f_4b39_a9dc_13183099c0e1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_33fe1755_151f_4b39_a9dc_13183099c0e1_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ HasPlanarDrawingOn M ∧
        ∃ (dM : DecidableRel M.Adj),
          (letI : DecidableRel M.Adj := dM;
            M.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_33fe1755_151f_4b39_a9dc_13183099c0e1_a1
      L hL hcard
  obtain ⟨dM, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_33fe1755_151f_4b39_a9dc_13183099c0e1_a1
      M hM hmax hcard
  exact ⟨M, hLM, hM, dM, hcount⟩