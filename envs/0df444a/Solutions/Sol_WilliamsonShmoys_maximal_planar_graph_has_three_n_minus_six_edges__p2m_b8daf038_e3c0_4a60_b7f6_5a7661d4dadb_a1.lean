-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_three_n_minus_six_edges__p2m_b8daf038_e3c0_4a60_b7f6_5a7661d4dadb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:53:17.038654+00:00
-- url     : https://prove2.me/submissions/487b5efc-9cc3-4a5b-8362-061f652deedf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_triangulating_extension__p2m_0a07d51a_b016_4e29_8963_bc66e107535c_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    3 * Fintype.card V = K.edgeFinset.card + 6 := by
  classical
  rcases WilliamsonShmoys.triangulating_extension__p2m_0a07d51a_b016_4e29_8963_bc66e107535c_a1
      K hV hK with ⟨L, hKL, hL, hCount⟩
  have hLK : L ≤ K := hmax L hKL hL
  have hGraph : L = K := le_antisymm hLK hKL
  subst L
  exact hCount
