-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_face_count_arithmetic__p2m_8700ddcb_5e54_440d_86e0_a8d22ebd60f0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:39:01.102819+00:00
-- url     : https://prove2.me/submissions/ef161594-9451-4500-b5e3-ff5aa76cb9e3

import Mathlib

set_option autoImplicit false

theorem solution
    (n f e : Nat) (faceLength : Fin f → Nat)
    (hEuler : n + f = e + 2)
    (hTotalLength : (∑ i : Fin f, faceLength i) = 2 * e)
    (hFaceLength : ∀ i : Fin f, 3 ≤ faceLength i) :
    e + 6 ≤ 3 * n := by
  have hsum : 3 * f ≤ ∑ i : Fin f, faceLength i := by
    calc
      3 * f = f * 3 := by omega
      _ = ∑ _i : Fin f, (3 : Nat) := by simp
      _ ≤ ∑ i : Fin f, faceLength i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hFaceLength i
  rw [hTotalLength] at hsum
  omega