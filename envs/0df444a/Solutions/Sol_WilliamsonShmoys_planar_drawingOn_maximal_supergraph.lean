-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:43:38.881969+00:00
-- url     : https://prove2.me/submissions/2f8833f7-2901-4bca-9d7c-70bd8554a83f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ M : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn M ∧ L.edgeSet ⊆ M.edgeSet ∧ ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N → M.edgeSet ⊆ N.edgeSet → N.edgeSet ⊆ M.edgeSet := by
  obtain ⟨M, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn L hL
  refine ⟨M, h2, SimpleGraph.edgeSet_subset_edgeSet.2 h1, fun N hNp hN => ?_⟩
  have := h3 N (SimpleGraph.edgeSet_subset_edgeSet.1 hN) hNp
  subst this
  exact fun _ h => h
