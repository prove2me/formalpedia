-- Prove2me | solution 1 for WilliamsonShmoys.face_walk_counting_bound__p2m_1aa142c3_2879_49d1_9ded_02a2d2269a9c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:39:10.422267+00:00
-- url     : https://prove2.me/submissions/313751f7-f6d6-40bd-aacb-04abcdfd9172

import Mathlib

set_option autoImplicit false

theorem len_le (l : List ℕ) (h : ∀ ℓ ∈ l, 3 ≤ ℓ) : 3 * l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a (by simp)
    have := ih (fun ℓ hl => h ℓ (by simp [hl]))
    simp only [List.length_cons, List.sum_cons]
    omega

theorem solution (e v : ℕ)
    (faceLengths : List ℕ)
    (hEuler : faceLengths.length = e - v + 2)
    (hSum : faceLengths.sum = 2 * e)
    (hFace : ∀ ℓ ∈ faceLengths, 3 ≤ ℓ) :
    e + 6 ≤ 3 * v := by
  have := len_le faceLengths hFace
  omega
