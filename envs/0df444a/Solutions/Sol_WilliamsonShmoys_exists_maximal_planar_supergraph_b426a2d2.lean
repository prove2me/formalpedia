-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_b426a2d2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:34:31.313369+00:00
-- url     : https://prove2.me/submissions/9f7ca7fa-10ed-4b69-9fec-b1c6b6783b90

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

-- A finite maximality argument: simple graphs on V form a finite set; maximize edge-set cardinality among the planar supergraphs of G. The drawing predicate and inclusion hypotheses are preserved by the selected family.

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
    ∃ U : SimpleGraph V,
      G ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧
        ∀ H : SimpleGraph V, U ≤ H →
          WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ U := by
  obtain ⟨U, h1, h2, h3⟩ := S181max _ G hG
  exact ⟨U, h1, h2, fun H hle hH => (h3 H hle hH).le⟩
