-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_e6f2f448_1eb8_42c3_a63b_d113f4e2074c_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:37:37.60513+00:00
-- url     : https://prove2.me/submissions/612c0994-7dce-4e19-a780-648e5165d4a8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  classical
  let S : Set (SimpleGraph V) :=
    {K | H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K}
  have hSfinite : S.Finite := Set.toFinite S
  obtain ⟨K, hKmem, hKmax⟩ :=
    hSfinite.exists_maximal (show S.Nonempty from ⟨H, le_rfl, hH⟩)
  change H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K at hKmem
  refine ⟨K, hKmem.1, hKmem.2, ?_⟩
  intro L hKL hL
  have hLmem : L ∈ S := ⟨hKmem.1.trans hKL, hL⟩
  have hLK : L ≤ K := hKmax hLmem hKL
  exact le_antisymm hLK hKL