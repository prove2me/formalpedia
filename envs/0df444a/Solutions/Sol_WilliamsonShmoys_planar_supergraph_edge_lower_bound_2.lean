-- Prove2me | solution 2 for WilliamsonShmoys.planar_supergraph_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T10:00:35.879367+00:00
-- url     : https://prove2.me/submissions/6db2e3cb-9473-483e-b36b-9d2dca9b6e2c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_edge_bound_93cad1d3_6631_4871_91db_d5199271705a

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    exists L : SimpleGraph V,
      K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  first
  | exact _root_.WilliamsonShmoys.planar_drawing_augmentation_edge_bound_93cad1d3_6631_4871_91db_d5199271705a
  | (apply _root_.WilliamsonShmoys.planar_drawing_augmentation_edge_bound_93cad1d3_6631_4871_91db_d5199271705a <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_drawing_augmentation_edge_bound_93cad1d3_6631_4871_91db_d5199271705a <;> assumption)
