-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_19c64167_1c0e_4c4b_ad8b_9aac5144fe63_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:25:36.121206+00:00
-- url     : https://prove2.me/submissions/b2929ffa-0a1d-4764-9ade-b4662d76e209

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_simpleGraph_exists_maximal_supergraph__p2m_ae09d195_ee8e_4c5a_9878_37e9ebede74b_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) :
    ∃ (T : SimpleGraph V) (dT : DecidableRel T.Adj),
      HasPlanarDrawingOn T ∧
      (letI : DecidableRel G.Adj := dG
       letI : DecidableRel T.Adj := dT
       G.edgeFinset ⊆ T.edgeFinset) ∧
      (∀ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
        HasPlanarDrawingOn U →
        (letI : DecidableRel T.Adj := dT
         letI : DecidableRel U.Adj := dU
         T.edgeFinset ⊆ U.edgeFinset) →
        T = U) := by
  exact finite_simpleGraph_exists_maximal_supergraph__p2m_ae09d195_ee8e_4c5a_9878_37e9ebede74b_a1
    HasPlanarDrawingOn G dG hG