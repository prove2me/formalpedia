-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_three_n_minus_six_edges__p2m_8f423dbe_14e3_49a1_828e_7cd49c2ddeb4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:57:55.034102+00:00
-- url     : https://prove2.me/submissions/55912056-7c77-4f98-aaa0-03a07771de44
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_2e383da1_b0fd_42ac_bf20_409641577930_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_2e383da1_b0fd_42ac_bf20_409641577930_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 = K.edgeFinset.card := by
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  have hu :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_2e383da1_b0fd_42ac_bf20_409641577930_a2
      K hcard hdraw
  have hl :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_2e383da1_b0fd_42ac_bf20_409641577930_a2
      K hcard hdraw hmax
  omega