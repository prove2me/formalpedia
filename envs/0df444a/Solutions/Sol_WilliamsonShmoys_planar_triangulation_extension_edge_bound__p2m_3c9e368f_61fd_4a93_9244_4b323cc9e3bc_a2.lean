-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_edge_bound__p2m_3c9e368f_61fd_4a93_9244_4b323cc9e3bc_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:26:25.373527+00:00
-- url     : https://prove2.me/submissions/39015aba-a66e-4c3a-811c-806bfbe3ddde
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_exists__p2m_74da5e6a_674d_4f79_986e_ea1a1f3184a0_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_74da5e6a_674d_4f79_986e_ea1a1f3184a0_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V) :
    Exists fun M : SimpleGraph V =>
      (forall {u v : V}, L.Adj u v -> M.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj
       3 * Fintype.card V - 6 <= M.edgeFinset.card) := by
  classical
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension_exists__p2m_74da5e6a_674d_4f79_986e_ea1a1f3184a0_a1
      L hL
  refine ⟨M, hLM, hM, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_74da5e6a_674d_4f79_986e_ea1a1f3184a0_a1
    M hM hcard hmax