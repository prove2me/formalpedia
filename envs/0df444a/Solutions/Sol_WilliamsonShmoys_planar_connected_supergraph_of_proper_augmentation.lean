-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_supergraph_of_proper_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:09:51.715236+00:00
-- url     : https://prove2.me/submissions/54382d8a-06c8-415c-9d60-f7407cb91d64

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hAugment : ∀ G : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ H : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn H ∧ G ≤ H ∧ G ≠ H) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧ Q.Connected ∧ P ≤ Q := by
  obtain ⟨M, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn P hP
  refine ⟨M, h2, ?_, h1⟩
  by_contra hc
  obtain ⟨H, hH, hMH, hne⟩ := hAugment M h2 hc
  exact hne (h3 H hMH hH).symm
