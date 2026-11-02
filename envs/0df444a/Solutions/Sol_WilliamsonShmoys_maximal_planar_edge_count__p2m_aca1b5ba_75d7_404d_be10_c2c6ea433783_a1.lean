-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_aca1b5ba_75d7_404d_be10_c2c6ea433783_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:39:31.171317+00:00
-- url     : https://prove2.me/submissions/803ff527-ca8c-4ede-924a-4a580d338525
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_extend_to_maximal_formula__p2m_f926186e_6933_42b8_b492_59096ed06c95_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : LE.le 3 (Fintype.card V))
    (hMax : forall N : SimpleGraph V, M <= N -> HasPlanarDrawingOn N -> N = M) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    M.edgeFinset.card + 6 = 3 * Fintype.card V := by
  letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  obtain ⟨N, hMN, hN, hEdgeCount⟩ :=
    WilliamsonShmoys.planar_graph_extend_to_maximal_formula__p2m_f926186e_6933_42b8_b492_59096ed06c95_a1
      M hM hcard
  have hNM : N = M := hMax N hMN hN
  subst N
  exact hEdgeCount