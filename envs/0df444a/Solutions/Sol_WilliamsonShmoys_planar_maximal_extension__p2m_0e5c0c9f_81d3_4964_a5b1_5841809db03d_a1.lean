-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_0e5c0c9f_81d3_4964_a5b1_5841809db03d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:26:04.233279+00:00
-- url     : https://prove2.me/submissions/f6128f01-f998-45cf-92d7-fc6ce623f903

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H := by
  classical
  let S : Set (SimpleGraph V) :=
    {H | K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H}
  have hSfin : S.Finite := by
    apply Set.Finite.subset Set.finite_univ
    intro H hH
    trivial
  have hSne : S.Nonempty := by
    exact ⟨K, le_rfl, hDraw⟩
  obtain ⟨H, hHmax⟩ := hSfin.exists_maximal hSne
  refine ⟨H, hHmax.1.1, hHmax.1.2, ?_⟩
  intro J hHJ hJ
  have hJmem : J ∈ S := by
    change K ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J
    exact ⟨hHmax.1.1.trans hHJ, hJ⟩
  have hJH : J ≤ H := hHmax.2 hJmem hHJ
  exact le_antisymm hJH hHJ