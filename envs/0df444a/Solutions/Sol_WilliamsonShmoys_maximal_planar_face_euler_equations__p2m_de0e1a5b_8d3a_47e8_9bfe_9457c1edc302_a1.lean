-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_euler_equations__p2m_de0e1a5b_8d3a_47e8_9bfe_9457c1edc302_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:21:12.758992+00:00
-- url     : https://prove2.me/submissions/c30b0d05-6914-429b-8704-400cc70351c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_4f918f75_55a8_4d80_8ca8_662e2486c7e0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (C : L.ConnectedComponent)
    (M : SimpleGraph C.supp)
    [Fintype C.supp]
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph C.supp, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M)
    (hcard : 3 ≤ C.supp.ncard) :
    ∃ f : ℕ,
      C.supp.ncard + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard := by
  have hE := WilliamsonShmoys.maximal_planar_edge_count__p2m_4f918f75_55a8_4d80_8ca8_662e2486c7e0_a1
    L C M hDraw hMax hcard
  refine ⟨2 * C.supp.ncard - 4, ?_, ?_⟩ <;> omega