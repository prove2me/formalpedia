-- Prove2me | solution 2 for ZipfLaw.zipfPMF_mean
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:31:26.033871+00:00
-- url     : https://prove2.me/submissions/e064d416-65de-403b-b171-b72b55db00b3

import Theorems.Thm_ZipfLaw_zipfPMF_moment
import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * zipfPMF N s k = genHarmonic N (s - 1) / genHarmonic N s := by
  simpa only [Nat.cast_one, pow_one] using zipfPMF_moment N s 1

#print axioms solution
