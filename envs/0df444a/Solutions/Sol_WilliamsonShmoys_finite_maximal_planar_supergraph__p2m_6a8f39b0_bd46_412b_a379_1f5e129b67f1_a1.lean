-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_6a8f39b0_bd46_412b_a379_1f5e129b67f1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:17:55.318269+00:00
-- url     : https://prove2.me/submissions/6bf7a5bd-c5ce-468f-8e43-6ff1761831be

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hSfinite : S.Finite := Set.toFinite S
  have hHmem : H ∈ S := ⟨le_rfl, hH⟩
  obtain ⟨K, hHK, hKmax⟩ := hSfinite.exists_le_maximal hHmem
  have hKmem : K ∈ S := hKmax.1
  have hKprop : H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K := hKmem
  refine ⟨K, hHK, hKprop.2, ?_⟩
  intro L hKL hL
  have hLmem : L ∈ S := ⟨hKprop.1.trans hKL, hL⟩
  exact hKmax.2 hLmem hKL