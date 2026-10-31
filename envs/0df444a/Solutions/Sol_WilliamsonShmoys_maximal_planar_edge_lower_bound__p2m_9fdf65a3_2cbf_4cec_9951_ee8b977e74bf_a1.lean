-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:05:54.373759+00:00
-- url     : https://prove2.me/submissions/229a41d5-ebf7-4b7e-b735-ebf966b05e6f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  have hMax' : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
    intro N hMN hDrawN
    exact hMax N (SimpleGraph.edgeSet_mono hMN) hDrawN
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition M hDraw hMax' hV
  omega