-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_exists_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:25:44.700504+00:00
-- url     : https://prove2.me/submissions/ddf90563-1e69-4c37-a6c9-f9ab54313ba0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_walks_mono_of_adj_inclusion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ u v : V, Nonempty (G.Walk u v)) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      (∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hGH, hH, hmax, hcard⟩ :=
    WilliamsonShmoys.finite_maximal_supergraph
      (V := V) G WilliamsonShmoys.HasPlanarDrawingOn hG
  have hconnH : ∀ u v : V, Nonempty (H.Walk u v) := by
    intro u v
    exact WilliamsonShmoys.walks_mono_of_adj_inclusion hGH (hconn u v)
  exact ⟨H, hGH, hH, hconnH, hmax, hcard⟩