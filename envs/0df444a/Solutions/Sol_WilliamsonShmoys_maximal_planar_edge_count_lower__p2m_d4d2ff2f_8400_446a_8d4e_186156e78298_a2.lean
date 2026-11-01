-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_d4d2ff2f_8400_446a_8d4e_186156e78298_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:05:14.73684+00:00
-- url     : https://prove2.me/submissions/0f6689ca-c503-4023-92ca-8bb196f14db8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_edge_count__p2m_cb206649_7371_4b65_b6a9_a6e949375fbf_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      3 * Fintype.card V - 6 ≤ K.edgeFinset.card) := by
  classical
  obtain ⟨L, hKL, hL, hEdges⟩ :=
    WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_cb206649_7371_4b65_b6a9_a6e949375fbf_a2
      K hK hcard
  have hLK : L = K := hmax L hKL hL
  subst L
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hEq : 3 * Fintype.card V - 6 = K.edgeFinset.card := by
    simpa using hEdges
  omega