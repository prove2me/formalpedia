-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_lower_from_maximal_planar_drawing_repair_025e7f85
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:17:55.084082+00:00
-- url     : https://prove2.me/submissions/aaa79fe2-184d-413a-9522-5cb6f7076f77

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_repair_025e7f85

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hDL, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_repair_025e7f85 K hK hCard
  have hEq : L = K := hMax L hKL hDL
  rw [← hEq]
  exact le_of_eq hCount