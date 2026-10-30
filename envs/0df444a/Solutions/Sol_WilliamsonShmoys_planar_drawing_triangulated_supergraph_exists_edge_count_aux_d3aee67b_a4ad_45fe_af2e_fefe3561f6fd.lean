-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulated_supergraph_exists_edge_count_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:26:31.953438+00:00
-- url     : https://prove2.me/submissions/22fcabff-b09f-4779-9e78-e9bf835de247

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_of_drawing_fc016acd_24e0_4b4c_9f94_11715a39d633
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_fc016acd_24e0_4b4c_9f94_11715a39d633

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L <= K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply Nat.le_antisymm
  all_goals first
    | exact WilliamsonShmoys.planar_edge_count_upper_bound_of_drawing_fc016acd_24e0_4b4c_9f94_11715a39d633 K hK hCard
    | exact WilliamsonShmoys.maximal_planar_edge_count_lower_bound_fc016acd_24e0_4b4c_9f94_11715a39d633 K hK hCard hMax
