-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_edge_maximal_extension_719c6bb7_9aa0_4725_9f39_6c34f4357440
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:01:36.38436+00:00
-- url     : https://prove2.me/submissions/80c12f8a-39e7-4d26-8010-ccb41fc02968

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

open WilliamsonShmoys in
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M ≤ N → HasPlanarDrawingOn N → N ≤ M := by
  obtain ⟨M, h1, h2, h3⟩ := S181max _ L hL
  exact ⟨M, h1, h2, fun N hMN hN => (h3 N hMN hN).le⟩
