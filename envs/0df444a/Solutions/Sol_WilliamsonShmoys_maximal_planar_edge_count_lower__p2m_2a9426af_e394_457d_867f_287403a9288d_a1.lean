-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_2a9426af_e394_457d_867f_287403a9288d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:41:51.69319+00:00
-- url     : https://prove2.me/submissions/d5ecd8e8-12c3-4ce4-a93a-5b2db5fda759

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_lower_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V) (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 ≤ H.edgeFinset.card := by
  classical
  have h := WilliamsonShmoys.planar_maximal_edge_lower_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1 H hdraw hcard hmax
  exact Nat.sub_le_iff_le_add.mpr h