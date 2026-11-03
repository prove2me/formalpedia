-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_1457b1f6_ab39_4e2c_8649_eee2274adac4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T12:00:22.236448+00:00
-- url     : https://prove2.me/submissions/10fe76d1-177c-42e9-9781-cae2c59104e3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_repair_20261027
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hdraw : HasPlanarDrawingOn N) :
    letI : forall H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  classical
  have he : N.edgeSet.ncard = N.edgeFinset.card := by
    rw [← N.coe_edgeFinset, Set.ncard_coe_finset]
  rw [← he]
  exact WilliamsonShmoys.planar_drawing_edge_count_upper_bound_repair_20261027 N hcard hdraw
