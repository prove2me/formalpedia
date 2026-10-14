-- Prove2me | solution 1 for ZipfLaw.zipfPMF_moment
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:28:31.162473+00:00
-- url     : https://prove2.me/submissions/0b56290f-a49f-437e-afa3-f9fb4ceef121

import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (N : ℕ) (s : ℝ) (p : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ p * zipfPMF N s k) =
      genHarmonic N (s - p) / genHarmonic N s := by
  rw [genHarmonic, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < (k : ℝ) := by
    have : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1
    exact_mod_cast this
  rw [zipfPMF, if_pos (Finset.mem_Icc.mp hk), Real.rpow_sub hkpos, Real.rpow_natCast]
  simp only [one_div_div]
  ring

#print axioms solution
