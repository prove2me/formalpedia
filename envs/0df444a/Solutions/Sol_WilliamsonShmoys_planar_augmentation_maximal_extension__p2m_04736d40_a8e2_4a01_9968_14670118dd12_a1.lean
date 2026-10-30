-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_maximal_extension__p2m_04736d40_a8e2_4a01_9968_14670118dd12_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:10:38.350865+00:00
-- url     : https://prove2.me/submissions/6a7901d0-0dff-44a6-bfa4-eb2c33aa01d8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by
  classical
  let S : Set (SimpleGraph V) := {K | H ≤ K ∧ HasPlanarDrawingOn K}
  have hSfinite : S.Finite := by
    exact Set.finite_univ.subset (Set.subset_univ S)
  have hSne : S.Nonempty := by
    refine ⟨H, ?_⟩
    change H ≤ H ∧ HasPlanarDrawingOn H
    exact ⟨le_rfl, hH⟩
  obtain ⟨K, hKmax⟩ := hSfinite.exists_maximal hSne
  have hK : K ∈ S := hKmax.1
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  have hLmem : L ∈ S := ⟨hK.1.trans hKL, hL⟩
  exact hKmax.2 hLmem hKL