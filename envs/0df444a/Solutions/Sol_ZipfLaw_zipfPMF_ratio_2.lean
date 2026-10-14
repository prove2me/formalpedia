-- Prove2me | solution 2 for ZipfLaw.zipfPMF_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:32:24.709601+00:00
-- url     : https://prove2.me/submissions/2634cc60-4955-44a4-b6e7-a06f1c822fb8

import Theorems.Thm_ZipfLaw_genHarmonic_pos
import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (N : ℕ) (s : ℝ) (n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    zipfPMF N s 1 / zipfPMF N s n = (n : ℝ) ^ s := by
  have hN : 1 ≤ N := le_trans hn1 hnN
  have hH := genHarmonic_pos N hN s
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hp := Real.rpow_pos_of_pos hnpos s
  have h1 : zipfPMF N s 1 = 1 / genHarmonic N s := by simp [zipfPMF, hN]
  rw [h1, zipfPMF, if_pos ⟨hn1, hnN⟩]
  field_simp [ne_of_gt hH, ne_of_gt hp]

#print axioms solution
