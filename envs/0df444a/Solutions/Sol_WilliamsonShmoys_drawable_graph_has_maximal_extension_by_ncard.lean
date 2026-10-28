-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_maximal_extension_by_ncard
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T11:54:03.117346+00:00
-- url     : https://prove2.me/submissions/f7601d86-b35c-4411-8ce7-eaf8eed29324

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

theorem S185nc {V : Type} [Fintype V] {G H : SimpleGraph V} (h : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.2 h) (Set.toFinite _)

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V, K ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ L : SimpleGraph V, M ≤ L → HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ M.edgeSet.ncard := by
  classical
  have hfin : ({J : SimpleGraph V | K ≤ J ∧ HasPlanarDrawingOn J}).Finite := Set.toFinite _
  obtain ⟨M, hM, hmax⟩ := Set.exists_max_image _ (fun J : SimpleGraph V => J.edgeSet.ncard) hfin ⟨K, le_rfl, hK⟩
  exact ⟨M, hM.1, hM.2, fun L hL hP => hmax L ⟨le_trans hM.1 hL, hP⟩⟩
