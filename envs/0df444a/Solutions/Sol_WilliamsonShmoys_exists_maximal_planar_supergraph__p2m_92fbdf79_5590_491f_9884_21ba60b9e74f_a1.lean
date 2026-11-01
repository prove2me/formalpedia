-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_92fbdf79_5590_491f_9884_21ba60b9e74f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:25:55.438438+00:00
-- url     : https://prove2.me/submissions/be9fce2d-1c11-4809-97ba-6d3ea8deeaea

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  let p : SimpleGraph V → Prop := fun H =>
    G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H
  obtain ⟨H, hGH, hmax⟩ :=
    Finite.exists_le_maximal (p := p) (a := G) ⟨le_rfl, hG⟩
  refine ⟨H, hGH, hmax.1.2, ?_⟩
  intro K hHK hK
  have hKH : K ≤ H := hmax.2 ⟨hGH.trans hHK, hK⟩ hHK
  exact le_antisymm hKH hHK