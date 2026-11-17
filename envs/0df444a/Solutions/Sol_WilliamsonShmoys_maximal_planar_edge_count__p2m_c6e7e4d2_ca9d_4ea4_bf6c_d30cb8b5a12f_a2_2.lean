-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_c6e7e4d2_ca9d_4ea4_bf6c_d30cb8b5a12f_a2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T08:00:24.530199+00:00
-- url     : https://prove2.me/submissions/f6f53353-4f66-4703-bd1e-13a1c40909af

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_790c0277_1cda_4997_aaa7_2744ce166f52_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    (letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
     N.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_790c0277_1cda_4997_aaa7_2744ce166f52_a1
    N hcard hN (fun L hL hle => hmax L hle hL)
