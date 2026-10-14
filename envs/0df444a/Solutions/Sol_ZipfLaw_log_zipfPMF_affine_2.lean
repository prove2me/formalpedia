-- Prove2me | solution 2 for ZipfLaw.log_zipfPMF_affine
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:32:25.514996+00:00
-- url     : https://prove2.me/submissions/509a3f9f-fe48-4152-bb32-2314d3bc0385

import Theorems.Thm_ZipfLaw_zipfPMF_ratio
import Theorems.Thm_ZipfLaw_genHarmonic_pos
import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (N : ℕ) (s : ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Real.log (zipfPMF N s k) = -s * Real.log k - Real.log (genHarmonic N s) := by
  have hN : 1 ≤ N := le_trans hk1 hkN
  have hH := genHarmonic_pos N hN s
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  have hpk : 0 < zipfPMF N s k := by
    rw [zipfPMF, if_pos ⟨hk1, hkN⟩]
    positivity
  have hp1 : 0 < zipfPMF N s 1 := by
    rw [zipfPMF, if_pos ⟨le_rfl, hN⟩]
    positivity
  have hlog := congrArg Real.log (zipfPMF_ratio N s k hk1 hkN)
  rw [Real.log_div hp1.ne' hpk.ne', Real.log_rpow hkpos] at hlog
  have hlog1 : Real.log (zipfPMF N s 1) = -Real.log (genHarmonic N s) := by
    simp [zipfPMF, hN, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hH.ne']
  rw [hlog1] at hlog
  linarith

#print axioms solution
