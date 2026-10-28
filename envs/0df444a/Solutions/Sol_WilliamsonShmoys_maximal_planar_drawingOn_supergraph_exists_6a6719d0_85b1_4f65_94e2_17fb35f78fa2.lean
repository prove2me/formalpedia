-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_supergraph_exists_6a6719d0_85b1_4f65_94e2_17fb35f78fa2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:30:54.859947+00:00
-- url     : https://prove2.me/submissions/6815d711-d522-4ec9-ba5a-55d2ade66d95

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
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun M : SimpleGraph V =>
      G <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      forall N : SimpleGraph V,
        M <= N ->
        WilliamsonShmoys.HasPlanarDrawingOn N ->
        N <= M := by
  obtain ⟨K, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn G hG
  exact ⟨K, h1, h2, fun L hL hQ => (h3 L hL hQ).le⟩
