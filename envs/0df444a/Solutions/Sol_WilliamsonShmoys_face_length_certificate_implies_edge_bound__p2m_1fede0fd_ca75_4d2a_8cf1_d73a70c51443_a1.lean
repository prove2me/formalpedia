-- Prove2me | solution 1 for WilliamsonShmoys.face_length_certificate_implies_edge_bound__p2m_1fede0fd_ca75_4d2a_8cf1_d73a70c51443_a1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:39:11.850466+00:00
-- url     : https://prove2.me/submissions/806e72a3-e56d-4d30-a83c-1c953aba2f35

import Mathlib

set_option autoImplicit false

theorem len_le (l : List Nat) (h : ∀ ℓ ∈ l, 3 ≤ ℓ) : 3 * l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a (by simp)
    have := ih (fun ℓ hl => h ℓ (by simp [hl]))
    simp only [List.length_cons, List.sum_cons]
    omega

theorem solution
    {n m : Nat} (faces : List Nat)
    (hN : 3 <= n)
    (hEuler : (n : Int) - (m : Int) + (faces.length : Int) = 2)
    (hSum : faces.sum = 2 * m)
    (hFace : ∀ length ∈ faces, 3 <= length) :
    (m : Int) <= 3 * (n : Int) - 6 := by
  have := len_le faces hFace
  omega
