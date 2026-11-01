-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_ffd766b2_d86f_4f00_bea0_c76fad60558a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:32:41.748725+00:00
-- url     : https://prove2.me/submissions/28706909-7cd8-468e-944d-741088cb6fa0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_edge_maximal_supergraph_for_finite_predicate__p2m_4cf1e2b2_149e_4f7a_8404_753e093946ad_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      (∀ P : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn P →
        (∀ u v, N.Adj u v → P.Adj u v) → P = N) := by
  obtain ⟨N, hN, hMN, hmax⟩ :=
    exists_edge_maximal_supergraph_for_finite_predicate__p2m_4cf1e2b2_149e_4f7a_8404_753e093946ad_a1
      (V := V) (R := WilliamsonShmoys.HasPlanarDrawingOn) (M := M) hM
  refine ⟨N, hN, hMN, ?_⟩
  intro P hP hNP
  exact hmax P hP (fun u v huv => hNP u v (hMN u v huv)) hNP