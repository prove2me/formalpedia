-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_0d2111fe_49a0_4983_b8b9_46fbb1acc127_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:15:04.708934+00:00
-- url     : https://prove2.me/submissions/09b26e85-979b-4629-bf1c-762ee46700f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_bound__p2m_ab59570c_fffd_4137_a2d3_71557bc91725_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : ∀ (P : SimpleGraph V),
      (∀ u v, G.Adj u v → P.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = G)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by
  obtain ⟨H, hExt, hH, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_edge_bound__p2m_ab59570c_fffd_4137_a2d3_71557bc91725_a1
      G hCard hG
  have hEq : H = G := hMax H hExt hH
  rw [hEq] at hCount
  exact hCount