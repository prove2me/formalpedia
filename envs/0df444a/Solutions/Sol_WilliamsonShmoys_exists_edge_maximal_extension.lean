-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:24.08244+00:00
-- url     : https://prove2.me/submissions/88bbdd9c-6278-4f06-ac3e-45610fbb8663

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] (P : SimpleGraph V → Prop)
    (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      P H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K ≤ H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ P J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2,
    Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hK.prop.1) (Set.toFinite _),
    fun N hN hPN => hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN⟩
