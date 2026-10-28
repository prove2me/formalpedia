-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_hereditary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:39:32.540808+00:00
-- url     : https://prove2.me/submissions/0961c18d-dc20-48d6-9ad9-d92c19d772fd

import Mathlib

set_option autoImplicit false

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hHereditary : ∀ G H : SimpleGraph V,
      Set.Subset G.edgeSet H.edgeSet → P H → P G)
    (K : SimpleGraph V)
    (hK : P K) :
    ∃ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet ∧
      P L ∧
      ∀ M : SimpleGraph V,
        Set.Subset L.edgeSet M.edgeSet →
        P M →
        M.edgeSet = L.edgeSet := by
  obtain ⟨L, h1, h2, h3⟩ := S181max P K hK
  exact ⟨L, SimpleGraph.edgeSet_mono h1, h2, fun M hM hPM => by
    rw [h3 M (SimpleGraph.edgeSet_subset_edgeSet.1 hM) hPM]⟩
