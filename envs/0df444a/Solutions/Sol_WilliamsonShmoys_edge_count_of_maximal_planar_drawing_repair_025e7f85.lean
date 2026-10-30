-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing_repair_025e7f85
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:44:51.04747+00:00
-- url     : https://prove2.me/submissions/5cd87e1e-768f-4f51-9b74-92a8ce53c671

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_count_upper_from_planar_drawing_repair_025e7f85
import Theorems.Thm_WilliamsonShmoys_edge_count_lower_from_maximal_planar_drawing_repair_025e7f85

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.edge_count_upper_from_planar_drawing_repair_025e7f85 K hK hCard
  have hLower :=
    WilliamsonShmoys.edge_count_lower_from_maximal_planar_drawing_repair_025e7f85
      K hK hCard hMax
  omega
