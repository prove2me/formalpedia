-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_edge_maximal__p2m_7b09e600_7df3_4cde_9f3e_028247bb9b4a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:30:02.28522+00:00
-- url     : https://prove2.me/submissions/34edcedf-e608-4e42-9ff0-31a2721a8eec

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by
  classical
  obtain ⟨H, hGH, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) hplanar)
  refine ⟨H, hGH, hmax.prop, ?_⟩
  intro K hHK hK
  exact (hmax.eq_of_le hK hHK).symm