-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_7f31c9a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:27:04.895108+00:00
-- url     : https://prove2.me/submissions/6cf25d5f-db99-4adf-8d1c-cbc455a99c6e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_77f664a0
import Theorems.Thm_WilliamsonShmoys_planar_triangulated_supergraph_77f664a0

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (H : SimpleGraph V)
    (hKH : ∀ u v, K.Adj u v → H.Adj u v)
    (hDrawH : HasPlanarDrawingOn H)
    (hmax : ∀ G : SimpleGraph V,
      (∀ u v, K.Adj u v → G.Adj u v) →
      HasPlanarDrawingOn G →
      G.edgeSet.ncard ≤ H.edgeSet.ncard) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨G, hHG, hDrawG, hGcount⟩ :=
    WilliamsonShmoys.planar_triangulated_supergraph_77f664a0 H hCard hDrawH
  have hGmax : G.edgeSet.ncard ≤ H.edgeSet.ncard := by
    apply hmax G
    · intro u v huv
      exact hHG u v (hKH u v huv)
    · exact hDrawG
  have hHbound : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_simple_edge_bound_77f664a0 H hCard hDrawH
  omega