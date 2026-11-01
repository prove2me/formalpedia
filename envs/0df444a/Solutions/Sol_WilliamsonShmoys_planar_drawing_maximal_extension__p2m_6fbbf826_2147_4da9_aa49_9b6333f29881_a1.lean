-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6fbbf826_2147_4da9_aa49_9b6333f29881_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:25:12.727213+00:00
-- url     : https://prove2.me/submissions/84478757-4649-4438-bbe9-d0b5901a3088

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_hereditary_simpleGraph_maximal_extension__p2m_73d27d15_d574_4133_8bc6_c15839fd5f47_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by
  have hhered : ∀ {G H : SimpleGraph V}, G ≤ H →
      HasPlanarDrawingOn H → HasPlanarDrawingOn G := by
    intro G H hGH hdraw
    rcases hdraw with ⟨p, arc, hp, hedge, hcross⟩
    refine ⟨p, arc, hp, ?_, ?_⟩
    · intro u v huv hadj
      exact hedge u v huv (hGH hadj)
    · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
      exact hcross u v x y huv hxy (hGH hadj) (hGH hadj') hne t ht s hs heq
  exact WilliamsonShmoys.finite_hereditary_simpleGraph_maximal_extension__p2m_73d27d15_d574_4133_8bc6_c15839fd5f47_a1
    HasPlanarDrawingOn hhered N hN