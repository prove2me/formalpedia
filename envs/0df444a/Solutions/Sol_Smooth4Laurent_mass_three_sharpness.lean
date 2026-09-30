-- Prove2me | solution 1 for Smooth4Laurent.mass_three_sharpness
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:01:57.429718+00:00
-- url     : https://prove2.me/submissions/1d5d8957-c669-407b-9e18-ab6948a76c40

import Mathlib

set_option autoImplicit false

theorem solution :
    let w : ℤ →₀ ℤ := Finsupp.single 0 1 + Finsupp.single 1 1 -
      Finsupp.single 2 1 + Finsupp.single 3 1 + Finsupp.single 4 1
    (∀ j : ℤ, 0 ≤ w j + w (j - 1)) ∧
      (∀ j : ℤ, 0 ≤ w j + w (j - 2)) ∧
      w.sum (fun _ a => a) = 3 ∧ w 2 = -1 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply]
    omega
  · intro j
    simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply]
    omega
  · norm_num [Finsupp.sum_add_index, Finsupp.sum_sub_index]
  · norm_num [Finsupp.single_apply]
