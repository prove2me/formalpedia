-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_maximal_supergraph__p2m_06bdf4fe_cd1d_4093_b45f_6118505c9d7e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:06:57.105762+00:00
-- url     : https://prove2.me/submissions/ee44ef79-ee87-470a-80ad-a63ee4535110

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_maximal_supergraph__p2m_03fd7227_be52_409b_9f5b_92650e994dba_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hKconn : K.Connected)
    (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       K.edgeFinset.card ≤ H.edgeFinset.card) ∧
      H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) := by
  obtain ⟨H, hKH, hHdraw, hmax⟩ :=
    WilliamsonShmoys.planar_extension_maximal_supergraph__p2m_03fd7227_be52_409b_9f5b_92650e994dba_a1
      K hKdraw
  refine ⟨H, hKH, ?_, hKconn.mono hKH, hHdraw, hmax⟩
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hKH)