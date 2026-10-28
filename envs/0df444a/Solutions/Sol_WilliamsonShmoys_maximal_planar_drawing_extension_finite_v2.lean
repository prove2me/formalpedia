-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_extension_finite_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:40.926054+00:00
-- url     : https://prove2.me/submissions/ba9631ba-6ef5-48e8-80b5-f94632dde2bc

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
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    Exists fun U : SimpleGraph V =>
      And (LE.le T U)
        (And (WilliamsonShmoys.HasPlanarDrawingOn U)
          (forall W : SimpleGraph V,
            LE.le U W -> WilliamsonShmoys.HasPlanarDrawingOn W -> W = U)) := by
  obtain ⟨K, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn T hT
  exact ⟨K, h1, h2, h3⟩
