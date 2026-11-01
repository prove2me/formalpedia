-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_planar_extension__p2m_4144dd03_670b_4445_9630_6cae19c82121_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:02:20.739688+00:00
-- url     : https://prove2.me/submissions/a0242ee5-9ce0-4c1d-8664-a46977714be1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph_of_downward_property__p2m_b2333537_9e91_4fe0_a355_0d6ef469faac_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V,
      (∀ u v, K.Adj u v → M.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V,
        (∀ u v, M.Adj u v → N.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        (∀ u v, N.Adj u v → M.Adj u v)) := by
  classical
  exact WilliamsonShmoys.finite_maximal_supergraph_of_downward_property__p2m_b2333537_9e91_4fe0_a355_0d6ef469faac_a1
    K WilliamsonShmoys.HasPlanarDrawingOn hK (by
      intro G H hGH hH
      rcases hH with ⟨p, arc, hp, hedge, hcross⟩
      refine ⟨p, arc, hp, ?_, ?_⟩
      · intro u v huv hGuv
        exact hedge u v huv (hGH u v hGuv)
      · intro u v x y huv hxy hGuv hGxy hne t ht s hs heq
        exact hcross u v x y huv hxy
          (hGH u v hGuv) (hGH x y hGxy) hne t ht s hs heq)