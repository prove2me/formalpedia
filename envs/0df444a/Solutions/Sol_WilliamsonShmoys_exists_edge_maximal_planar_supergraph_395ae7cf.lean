-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph_395ae7cf
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T13:43:41.966983+00:00
-- url     : https://prove2.me/submissions/dab67cc0-46b7-48c6-a9ad-d2b0b236e10e

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
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V, H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G ∧
      ∀ J : SimpleGraph V, G ≤ J →
        WilliamsonShmoys.HasPlanarDrawingOn J → J = G :=
  S181max _ H hH
