-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_3fec8f0c_c3a7_4eba_b2f0_d2b6c5de2dde_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:55:23.715633+00:00
-- url     : https://prove2.me/submissions/f9bb10da-4625-438e-9908-cb214e796092

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_edge_count__p2m_3a830fa8_5714_4871_98bd_724059b55494_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hEdges⟩ :=
    WilliamsonShmoys.planar_augmentation_edge_count__p2m_3a830fa8_5714_4871_98bd_724059b55494_a2
      H hH hCard
  have hKH : K = H := hMax K hHK hK
  subst K
  omega