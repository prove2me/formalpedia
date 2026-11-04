-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:39:17.091554+00:00
-- url     : https://prove2.me/submissions/387e509a-db39-430e-b24c-1d5e95f34738

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_lower_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, HasPlanarDrawingOn N → M ≤ N → N = M) :
    3 * Fintype.card V - 6 ≤
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj
       M.edgeFinset.card) := by
  have h := WilliamsonShmoys.planar_maximal_edge_lower_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1
    M hM hcard (fun N hMN hN => hmax N hN hMN)
  omega

