-- Prove2me | solution 1 for ZipfLaw.zipfPMF_variance
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:48:40.850609+00:00
-- url     : https://prove2.me/submissions/bc8d9795-3d4f-4d70-93cd-23b62cada641

import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

private lemma moment_sum (N : ℕ) (s : ℝ) (p : ℕ) :
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

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ 2 * zipfPMF N s k) -
        (∑ k ∈ Finset.Icc 1 N, (k : ℝ) * zipfPMF N s k) ^ 2 =
      genHarmonic N (s - 2) / genHarmonic N s -
        genHarmonic N (s - 1) ^ 2 / genHarmonic N s ^ 2 := by
  have hfirst := moment_sum N s 1
  simp only [Nat.cast_one, pow_one] at hfirst
  rw [moment_sum N s 2, hfirst, div_pow]
  norm_num

#print axioms solution

