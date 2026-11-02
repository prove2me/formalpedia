-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_common_face_count__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:53:54.179314+00:00
-- url     : https://prove2.me/submissions/920819bb-c51a-4c38-a35c-2f37324c25c2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_91ffed91_b87b_43c6_ba27_69e25b4e372c_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    ∃ f : ℕ,
      Fintype.card V + f = N.edgeFinset.card + 2 ∧
      3 * f = 2 * N.edgeFinset.card := by
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  have hE := WilliamsonShmoys.maximal_planar_edge_count__p2m_91ffed91_b87b_43c6_ba27_69e25b4e372c_a1
    N hN hconn hcard hmax
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩
  · omega
  · omega