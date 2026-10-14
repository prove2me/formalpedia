-- Prove2me | solution 1 for ZipfLaw.zipf_summable_iff
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:28:29.568958+00:00
-- url     : https://prove2.me/submissions/5f2f6c32-d0ac-4ae8-8455-6f88bea9c38f

import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (s : ℝ) (hs : 0 ≤ s) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) ↔ 1 < s := by
  have h := Real.summable_one_div_nat_add_rpow 1 s
  have habs : ∀ k : ℕ, |(k : ℝ) + 1| = (k : ℝ) + 1 := fun k =>
    abs_of_pos (by positivity)
  simpa only [habs] using h

#print axioms solution
