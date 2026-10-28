-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_maximal_planar_completion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:20:04.584773+00:00
-- url     : https://prove2.me/submissions/f633a894-6ae4-41d6-bfcd-f7c842ef62bf

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
    (hV : 3 <= Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    exists H' : SimpleGraph V,
      H <= H' ∧
      WilliamsonShmoys.HasPlanarDrawingOn H' ∧
      (∀ K : SimpleGraph V, H' <= K → K ≠ H' →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn K) := by
  obtain ⟨K, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn H hH
  exact ⟨K, h1, h2, fun L hL hne hd => hne (h3 L hL hd)⟩
