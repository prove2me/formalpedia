-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:28:46.802045+00:00
-- url     : https://prove2.me/submissions/810b4987-17cd-452b-b129-f4e4aabdd3f9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn L ∧ K.edgeSet ⊆ L.edgeSet ∧ (∀ M : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn M → L.edgeSet ⊆ M.edgeSet → M.edgeSet ⊆ L.edgeSet) := by
  obtain ⟨M, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn K hK
  refine ⟨M, h2, SimpleGraph.edgeSet_subset_edgeSet.2 h1, fun N hNp hN => ?_⟩
  have := h3 N (SimpleGraph.edgeSet_subset_edgeSet.1 hN) hNp
  subst this
  exact fun _ h => h
