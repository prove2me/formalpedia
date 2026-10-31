-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_edge_bound__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a2__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:21:46.982931+00:00
-- url     : https://prove2.me/submissions/14d645e7-8205-438a-9acd-9450d5ad4113

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (h : exists f : Nat, Fintype.card V + f = K.edgeSet.ncard + 2 /\ 3 * f = 2 * K.edgeSet.ncard) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  cases h with
  | intro f hf =>
    cases hf with
    | intro hEuler hIncidence =>
      omega