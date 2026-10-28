-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph_dense_ext
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:20:01.535276+00:00
-- url     : https://prove2.me/submissions/5294ec0a-ddfe-439f-b1a4-7c2f89777acf

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
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    exists P : SimpleGraph V, N <= P /\ WilliamsonShmoys.HasPlanarDrawingOn P /\
      forall Q : SimpleGraph V, P <= Q -> WilliamsonShmoys.HasPlanarDrawingOn Q -> Q <= P := by
  obtain ⟨K, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn N hN
  exact ⟨K, h1, h2, fun L hL hd => (h3 L hL hd).le⟩
