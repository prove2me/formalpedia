-- Prove2me | solution 2 for WilliamsonShmoys.drawable_supergraph_maximal_aea3a4e2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:09:57.857979+00:00
-- url     : https://prove2.me/submissions/55eafe92-80a9-41d8-81e5-5743c8e9ec3b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      Set.Subset H.edgeSet K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, Set.Subset K.edgeSet L.edgeSet →
        HasPlanarDrawingOn L → Set.Subset L.edgeSet K.edgeSet) := by
  obtain ⟨M, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn H hH
  refine ⟨M, SimpleGraph.edgeSet_subset_edgeSet.2 h1, h2, fun N hN hNp => ?_⟩
  have := h3 N (SimpleGraph.edgeSet_subset_edgeSet.1 hN) hNp
  subst this
  exact fun _ h => h
