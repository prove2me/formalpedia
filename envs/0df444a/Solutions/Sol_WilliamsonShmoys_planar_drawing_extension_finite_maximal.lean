-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extension_finite_maximal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:47:00.454756+00:00
-- url     : https://prove2.me/submissions/eacf9be6-ff99-4a63-b1bc-a374b4e7c8a2

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
    (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      N.edgeSet ⊆ P.edgeSet ∧
      ∀ Q : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn Q →
        P.edgeSet ⊆ Q.edgeSet → Q.edgeSet ⊆ P.edgeSet := by
  obtain ⟨P, h1, h2, h3⟩ := S181max _ N hN
  refine ⟨P, h2, SimpleGraph.edgeSet_subset_edgeSet.2 h1, fun Q hQ hs => ?_⟩
  rw [h3 Q (SimpleGraph.edgeSet_subset_edgeSet.1 hs) hQ]
