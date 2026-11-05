-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:29:36.782208+00:00
-- url     : https://prove2.me/submissions/28760df6-6e62-420b-9112-e6e200bc32cc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_triangulate_planar_graph_on_same_vertices__p2m_9bc8f5f5_22dd_4255_9d37_0a6f5ce9c2a7_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨N, hNplanar, hMN, hNedges⟩ :=
    WilliamsonShmoys.triangulate_planar_graph_on_same_vertices__p2m_9bc8f5f5_22dd_4255_9d37_0a6f5ce9c2a7_a2
      M hplanar hcard
  have hNM : N = M := hmax N hNplanar hMN
  subst N
  omega
