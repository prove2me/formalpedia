-- Prove2me | solution 2 for ZipfLaw.zipfPMF_mode
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:32:26.276175+00:00
-- url     : https://prove2.me/submissions/e061d8da-68e6-4fac-8285-14cdf522f874

import Theorems.Thm_ZipfLaw_zipfPMF_ratio
import Theorems.Thm_ZipfLaw_genHarmonic_pos
import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    zipfPMF N s k ≤ zipfPMF N s 1 := by
  have hH := genHarmonic_pos N hN s
  have h1 : zipfPMF N s 1 = 1 / genHarmonic N s := by simp [zipfPMF, hN]
  by_cases hk : 1 ≤ k ∧ k ≤ N
  · have hpk : 0 < zipfPMF N s k := by
      rw [zipfPMF, if_pos hk]
      have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk.1)
      positivity
    have hratio : 1 ≤ zipfPMF N s 1 / zipfPMF N s k := by
      rw [zipfPMF_ratio N s k hk.1 hk.2]
      exact Real.one_le_rpow (by exact_mod_cast hk.1) hs
    simpa using (le_div_iff₀ hpk).mp hratio
  · rw [zipfPMF, if_neg hk, h1]
    positivity

#print axioms solution
