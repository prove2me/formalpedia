-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_3c187467_059b_4073_9a0b_83e3bfc104a1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:20:51.539925+00:00
-- url     : https://prove2.me/submissions/b7c26b49-0c6e-4a80-9364-af391e05cde5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_11371f3f_0d50_4c49_9eed_89dfd5ac185f_a1
import Theorems.Thm_WilliamsonShmoys_finite_subgraph_maximal__p2m_11371f3f_0d50_4c49_9eed_89dfd5ac185f_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V) (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, Z.Adj u v → H.Adj u v) ∧
      Z.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K = H := by
  have hdown : ∀ {G H : SimpleGraph V},
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn H →
      WilliamsonShmoys.HasPlanarDrawingOn G := by
    intro G H hGH hH
    exact WilliamsonShmoys.planar_drawing_subgraph__p2m_11371f3f_0d50_4c49_9eed_89dfd5ac185f_a1 hGH hH
  exact WilliamsonShmoys.finite_subgraph_maximal__p2m_11371f3f_0d50_4c49_9eed_89dfd5ac185f_a1
    Z WilliamsonShmoys.HasPlanarDrawingOn hZ hdown
