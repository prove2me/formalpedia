-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_euler_face_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T03:39:57.868965+00:00
-- url     : https://prove2.me/submissions/79d96711-3930-4b91-86fe-56f3aeef922b

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = K.edgeSet.ncard + 2)
    (hTri : 3 * f = 2 * K.edgeSet.ncard) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by omega
