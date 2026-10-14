-- Prove2me | solution 2 for ZipfLaw.zipfPMF_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:32:23.981654+00:00
-- url     : https://prove2.me/submissions/aa15d04d-3365-47e6-8432-89c526ad4181

import Theorems.Thm_ZipfLaw_zipfPMF_cdf
import Theorems.Thm_ZipfLaw_genHarmonic_pos
import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    ∑ k ∈ Finset.Icc 1 N, zipfPMF N s k = 1 := by
  rw [zipfPMF_cdf N hN s N le_rfl]
  exact div_self (genHarmonic_pos N hN s).ne'

#print axioms solution
