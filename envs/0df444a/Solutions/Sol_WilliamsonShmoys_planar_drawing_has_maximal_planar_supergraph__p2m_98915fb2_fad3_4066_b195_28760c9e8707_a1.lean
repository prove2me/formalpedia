-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph__p2m_98915fb2_fad3_4066_b195_28760c9e8707_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:47:23.201317+00:00
-- url     : https://prove2.me/submissions/5ebf39a8-63d2-4411-8d97-05546014838a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V, Q ≤ R ∧ WilliamsonShmoys.HasPlanarDrawingOn R ∧
      ∀ S : SimpleGraph V, R ≤ S → WilliamsonShmoys.HasPlanarDrawingOn S → S = R := by
  classical
  let admissible : Set (SimpleGraph V) :=
    {R | Q ≤ R ∧ WilliamsonShmoys.HasPlanarDrawingOn R}
  have hfinite : admissible.Finite := Set.toFinite admissible
  have hnonempty : admissible.Nonempty := ⟨Q, le_rfl, hQ⟩
  obtain ⟨R, hR, hmax⟩ := hfinite.exists_maximal hnonempty
  refine ⟨R, hR.1, hR.2, ?_⟩
  intro S hRS hS
  have hSmem : S ∈ admissible := ⟨hR.1.trans hRS, hS⟩
  have hSR : S ≤ R := hmax hSmem hRS
  exact le_antisymm hSR hRS