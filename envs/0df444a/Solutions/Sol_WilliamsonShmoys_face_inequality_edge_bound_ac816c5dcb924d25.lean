-- Prove2me | solution 1 for WilliamsonShmoys.face_inequality_edge_bound_ac816c5dcb924d25
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:17:10.326536+00:00
-- url     : https://prove2.me/submissions/930021c9-f540-4ee4-8109-407b7e783a24

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (f : Nat)
    (hEuler : Fintype.card V + f = H.edgeSet.ncard + 2)
    (hFaces : 3 * f ≤ 2 * H.edgeSet.ncard) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  omega