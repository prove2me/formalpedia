-- Prove2me | solution 1 for WilliamsonShmoys.finite_planar_supergraph_maximal_connected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:39:31.157194+00:00
-- url     : https://prove2.me/submissions/7946820a-417a-4a49-812e-52b77869f544

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

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hStep : ∀ K : SimpleGraph V,
      G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      ¬ K.Connected →
      ∃ L : SimpleGraph V,
        K < L ∧ WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨K, h1, h2, h3⟩ := S181max (fun K => G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K) G ⟨le_rfl, hG⟩
  refine ⟨K, h2.1, ?_, h2.2, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono h2.1) (Set.toFinite _)⟩
  by_contra hc
  obtain ⟨L, hlt, hL⟩ := hStep K h2.1 h2.2 hc
  have := h3 L hlt.le ⟨h2.1.trans hlt.le, hL⟩
  subst this
  exact lt_irrefl _ hlt
