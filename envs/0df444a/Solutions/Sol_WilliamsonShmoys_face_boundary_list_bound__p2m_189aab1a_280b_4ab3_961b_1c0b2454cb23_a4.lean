-- Prove2me | solution 1 for WilliamsonShmoys.face_boundary_list_bound__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T19:15:04.000653+00:00
-- url     : https://prove2.me/submissions/a2ccd77e-ac5c-4167-87f5-465729bfdae1

import Mathlib

set_option autoImplicit false

theorem solution
    (lengths : List ℕ)
    (hLower : ∀ x ∈ lengths, 3 ≤ x) :
    3 * lengths.length ≤ lengths.sum := by
  have h : ∀ l : List ℕ, (∀ x ∈ l, 3 ≤ x) → 3 * l.length ≤ l.sum := by
    intro l
    induction l with
    | nil =>
        intro _
        simp
    | cons a l ih =>
        intro hl
        have ha : 3 ≤ a := hl a (by simp)
        have htail : ∀ x ∈ l, 3 ≤ x := by
          intro x hx
          exact hl x (by simp [hx])
        have hsum := ih htail
        simp only [List.length_cons, List.sum_cons]
        omega
  exact h lengths hLower