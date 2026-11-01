-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_c643eab9_16cc_4e69_8d73_dd1e68fa5bd2_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:21:12.488087+00:00
-- url     : https://prove2.me/submissions/fd08eb1a-6cef-4d87-981c-0e6651a0fe7f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_58dc5ab1_94a9_407e_bf9a_7b232f0762ef_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hW : HasPlanarDrawingOn W) :
    letI : DecidableRel W.Adj := Classical.decRel W.Adj
    ∃ H : SimpleGraph V, HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       W.edgeFinset ⊆ H.edgeFinset) ∧
      ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
        (letI : DecidableRel H.Adj := Classical.decRel H.Adj
         letI : DecidableRel K.Adj := Classical.decRel K.Adj
         H.edgeFinset ⊆ K.edgeFinset → K.edgeFinset ⊆ H.edgeFinset) := by
  classical
  letI : DecidableRel W.Adj := Classical.decRel W.Adj
  exact WilliamsonShmoys.finite_maximal_extension__p2m_58dc5ab1_94a9_407e_bf9a_7b232f0762ef_a1
    W HasPlanarDrawingOn hW