-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_arithmetic_282b0fbb
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T10:53:23.654499+00:00
-- url     : https://prove2.me/submissions/d5ee85ac-0110-44cf-9a5e-0b9b555c77df

import Mathlib

set_option autoImplicit false
theorem solution
    (n m : ℕ) (faces : List ℕ)
    (hCard : 3 <= n)
    (hEuler : (n : Int) - (m : Int) + (faces.length : Int) = 2)
    (hIncidence : faces.sum = 2 * m)
    (hFaceLength : ∀ f, f ∈ faces → 3 <= f) :
    (m : Int) <= 3 * (n : Int) - 6 := by
  have key : ∀ l : List ℕ, (∀ f, f ∈ l → 3 <= f) → 3 * l.length ≤ l.sum := by
    intro l hl
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.length_cons, List.sum_cons]
      have := hl a (by simp)
      have := ih (fun f hf => hl f (by simp [hf]))
      omega
  have := key faces hFaceLength
  omega
