-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:37:45.891309+00:00
-- url     : https://prove2.me/submissions/de94deef-75c0-4f9e-88ac-50066e0a364d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_element_of_finite_predicate__p2m_5205e6ef_38db_4828_a550_3d962d50da00_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  classical
  let P : SimpleGraph V → Prop := fun G => H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hP : ∃ G, P G := ⟨H, le_rfl, hH⟩
  obtain ⟨K, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_element_of_finite_predicate__p2m_5205e6ef_38db_4828_a550_3d962d50da00_a2
      P hP
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  have hPL : P L := ⟨hK.1.trans hKL, hL⟩
  have hLK : L ≤ K := hmax L hPL hKL
  exact le_antisymm hLK hKL