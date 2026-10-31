-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_aea893ff_524d_432f_a94f_a28f6a185e5e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:40:11.146181+00:00
-- url     : https://prove2.me/submissions/fa7d7acf-e099-4b61-8817-563942e6a9f2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_8dfa4b72_07b4_4156_b232_5425c6bb73fa_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hCount⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation__p2m_8dfa4b72_07b4_4156_b232_5425c6bb73fa_a1
      K hCard hK
  have hEq : L = K := hmax L hKL hL
  simpa [hEq] using hCount