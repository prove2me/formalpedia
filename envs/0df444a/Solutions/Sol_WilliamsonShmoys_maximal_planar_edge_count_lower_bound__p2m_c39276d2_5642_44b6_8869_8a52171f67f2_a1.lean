-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c39276d2_5642_44b6_8869_8a52171f67f2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:11:33.18612+00:00
-- url     : https://prove2.me/submissions/07b1fcb9-ebc4-42f8-815a-0abdde2f2b54

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_efbdf66e_6b79_4361_98ec_bc960d2ecfa5_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨L, hKL, hLDraw, hEdges⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_efbdf66e_6b79_4361_98ec_bc960d2ecfa5_a1
      K hDraw hV
  have hLK : L = K := hMax L hKL hLDraw
  rw [← hLK]
  exact le_of_eq hEdges