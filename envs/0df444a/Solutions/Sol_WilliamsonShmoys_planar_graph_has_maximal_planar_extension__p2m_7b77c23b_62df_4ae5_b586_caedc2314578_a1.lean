-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_maximal_planar_extension__p2m_7b77c23b_62df_4ae5_b586_caedc2314578_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:11:51.556207+00:00
-- url     : https://prove2.me/submissions/705b7a63-1f32-4738-8f59-207499458b8e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_of_finite__p2m_0bdc9ebc_c764_435b_b9dd_f3dd83a4d5eb_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  classical
  let P : SimpleGraph V → Prop := fun G => H ≤ G ∧ HasPlanarDrawingOn G
  have hP : P H := ⟨le_rfl, hplanar⟩
  obtain ⟨K, hK, hmax⟩ :=
    exists_maximal_of_finite__p2m_0bdc9ebc_c764_435b_b9dd_f3dd83a4d5eb_a1 P H hP
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  exact hmax L hKL ⟨le_trans hK.1 hKL, hL⟩