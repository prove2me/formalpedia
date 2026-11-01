-- Prove2me | solution 1 for WilliamsonShmoys.nat_face_length_distribution__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:47:33.279194+00:00
-- url     : https://prove2.me/submissions/7395cc80-1d72-403f-9c97-edc7ee0690eb

import Mathlib
import Theorems.Thm_WilliamsonShmoys_face_length_distribution_of_budget__p2m_1141cd9b_272f_416d_a43b_8cf00258b943_a1

set_option autoImplicit false

theorem solution
    (n E f : Nat)
    (hEuler : n + f = E + 2)
    (hBound : E + 6 ≤ 3 * n)
    (hf : 0 < f) :
    ∃ faceLength : Fin f → Nat,
      (∑ i : Fin f, faceLength i) = 2 * E ∧
      ∀ i : Fin f, 3 ≤ faceLength i := by
  have hBudget : 3 * f ≤ 2 * E := by omega
  exact WilliamsonShmoys.face_length_distribution_of_budget__p2m_1141cd9b_272f_416d_a43b_8cf00258b943_a1
    f (2 * E) hf hBudget