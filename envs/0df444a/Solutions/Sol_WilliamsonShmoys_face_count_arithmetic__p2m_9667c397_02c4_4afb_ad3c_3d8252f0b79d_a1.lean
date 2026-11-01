-- Prove2me | solution 1 for WilliamsonShmoys.face_count_arithmetic__p2m_9667c397_02c4_4afb_ad3c_3d8252f0b79d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:18:29.58561+00:00
-- url     : https://prove2.me/submissions/58caf309-ff2d-4aa1-8778-08e080ff8137

import Mathlib

set_option autoImplicit false

theorem solution
    (n m f : Nat) (len : Fin f -> Nat)
    (heuler : n + f = m + 2)
    (hinc : Finset.univ.sum (fun i : Fin f => len i) = 2 * m)
    (htri : forall i : Fin f, len i = 3) :
    3 * n <= m + 6 := by
  have hsum : f * 3 = 2 * m := by
    simpa [htri, Finset.sum_const, Finset.card_fin] using hinc
  omega