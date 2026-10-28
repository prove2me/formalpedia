-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_for_completion_20261026
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:09:55.684157+00:00
-- url     : https://prove2.me/submissions/db8f5776-e074-4f0d-9e68-07e2109b3f25

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
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ L : SimpleGraph V, M ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ M := by
  obtain ⟨M, h1, h2, h3⟩ := S181max _ H hHdraw
  exact ⟨M, h1, h2, fun L hle hL => (h3 L hle hL).le⟩
