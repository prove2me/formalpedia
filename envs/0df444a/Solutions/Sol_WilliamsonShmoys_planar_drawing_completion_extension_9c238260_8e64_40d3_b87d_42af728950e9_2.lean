-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_completion_extension_9c238260_8e64_40d3_b87d_42af728950e9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:38.772058+00:00
-- url     : https://prove2.me/submissions/e80854cf-5c66-4ff0-b34f-83fc11bc8804

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDrawing : HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H := by
  obtain ⟨K, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn G hDrawing
  exact ⟨K, h1, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono h1) (Set.toFinite _), h2,
    fun L hL hQ => (h3 L hL hQ).le⟩
