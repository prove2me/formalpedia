-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_equations__p2m_6a93ee10_5962_45c7_890c_230c5f08b7cb_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:52:08.111336+00:00
-- url     : https://prove2.me/submissions/7877748d-44ea-4f71-97b2-71df3f29d83a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_ce063170_d1d4_44ee_8dd5_42d3412301d5_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_ce063170_d1d4_44ee_8dd5_42d3412301d5_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    exists f : Nat,
      And (Fintype.card V + f = L.edgeFinset.card + 2)
          (3 * f = 2 * L.edgeFinset.card) := by
  classical
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  have hupper := WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_ce063170_d1d4_44ee_8dd5_42d3412301d5_a1 L hL hmax hcard
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ce063170_d1d4_44ee_8dd5_42d3412301d5_a1 L hL hmax hcard
  refine Exists.intro (2 * Fintype.card V - 4) (And.intro ?_ ?_) <;> omega