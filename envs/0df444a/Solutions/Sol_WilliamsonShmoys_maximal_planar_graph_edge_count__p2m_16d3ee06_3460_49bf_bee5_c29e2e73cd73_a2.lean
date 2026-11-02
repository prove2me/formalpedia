-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_16d3ee06_3460_49bf_bee5_c29e2e73cd73_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:55:13.836726+00:00
-- url     : https://prove2.me/submissions/1439a4e4-67d3-414e-b3be-5252d9def14f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension__p2m_077d3f0d_ff79_48f3_bde0_954cbd7dcf68_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hmax : forall J : SimpleGraph V, HasPlanarDrawingOn J -> H <= J -> J = H)
    (hcard : 3 <= Fintype.card V) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  let hExt :=
    WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_077d3f0d_ff79_48f3_bde0_954cbd7dcf68_a2
      H hH hcard
  let J := Classical.choose hExt
  have hJ : HasPlanarDrawingOn J := (Classical.choose_spec hExt).1
  have hHJ : H <= J := (Classical.choose_spec hExt).2.1
  have hcount : J.edgeFinset.card = 3 * Fintype.card V - 6 :=
    (Classical.choose_spec hExt).2.2
  have hEq : J = H := hmax J hJ hHJ
  rw [hEq] at hcount
  exact hcount