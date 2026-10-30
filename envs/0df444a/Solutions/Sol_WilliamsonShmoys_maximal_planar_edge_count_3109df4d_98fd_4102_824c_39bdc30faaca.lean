-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_3109df4d_98fd_4102_824c_39bdc30faaca
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:42:13.977976+00:00
-- url     : https://prove2.me/submissions/33554a26-6c6b-472c-9046-3acf73cf6d8f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_f1bfaff0_3b11_4c21_8672_bb1e9fe098b3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_f1bfaff0_3b11_4c21_8672_bb1e9fe098b3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, HasPlanarDrawingOn L →
      (∀ u v, K.Adj u v → L.Adj u v) →
      ∀ u v, L.Adj u v → K.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.maximal_planar_edge_count_upper_f1bfaff0_3b11_4c21_8672_bb1e9fe098b3 K hK hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_f1bfaff0_3b11_4c21_8672_bb1e9fe098b3 K hK hMax hCard
  omega