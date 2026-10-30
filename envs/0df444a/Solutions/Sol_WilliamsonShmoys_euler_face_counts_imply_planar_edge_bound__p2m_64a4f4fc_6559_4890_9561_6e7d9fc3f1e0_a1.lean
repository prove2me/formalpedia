-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_counts_imply_planar_edge_bound__p2m_64a4f4fc_6559_4890_9561_6e7d9fc3f1e0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:19:14.468763+00:00
-- url     : https://prove2.me/submissions/62dee26e-b3c8-4523-8334-5ad395bf3efd

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = K.edgeSet.ncard + 2)
    (hFaces : 3 * f = 2 * K.edgeSet.ncard) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  omega