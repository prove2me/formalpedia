-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph_b5197173
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:48:11.921484+00:00
-- url     : https://prove2.me/submissions/8c83c12c-a116-44cf-876a-db8192db0746

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    Exists (fun N : SimpleGraph V =>
      And (M <= N)
        (And (WilliamsonShmoys.HasPlanarDrawingOn N)
          (∀ P : SimpleGraph V, N <= P →
            WilliamsonShmoys.HasPlanarDrawingOn P → P = N))) := by
  exact S181max WilliamsonShmoys.HasPlanarDrawingOn M hM
