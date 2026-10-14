-- Prove2me | solution 1 for ZipfLaw.genHarmonic_pos
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:28:30.311659+00:00
-- url     : https://prove2.me/submissions/cb10c320-bff2-4a3a-a9e6-2be3451e0d57

import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) : 0 < genHarmonic N s := by
  unfold genHarmonic
  exact Finset.sum_pos' (fun k _ => by positivity)
    ⟨1, by simp [hN], by norm_num⟩

#print axioms solution
