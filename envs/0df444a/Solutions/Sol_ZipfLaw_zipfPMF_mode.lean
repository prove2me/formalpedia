-- Prove2me | solution 1 for ZipfLaw.zipfPMF_mode
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:48:42.454265+00:00
-- url     : https://prove2.me/submissions/5fff41e5-7532-4180-93d4-b65d0395dee0

import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

private lemma zipf_harmonic_pos (N : ℕ) (hN : 1 ≤ N) (s : ℝ) : 0 < genHarmonic N s := by
  unfold genHarmonic
  exact Finset.sum_pos' (fun k _ => by positivity)
    ⟨1, by simp [hN], by norm_num⟩

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    zipfPMF N s k ≤ zipfPMF N s 1 := by
  have hH := zipf_harmonic_pos N hN s
  have h1 : zipfPMF N s 1 = 1 / genHarmonic N s := by simp [zipfPMF, hN]
  rw [h1]
  by_cases hk : 1 ≤ k ∧ k ≤ N
  · rw [zipfPMF, if_pos hk]
    apply div_le_div_of_nonneg_right _ (le_of_lt hH)
    have hbase : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
    simpa using one_div_le_one_div_of_le zero_lt_one (Real.one_le_rpow hbase hs)
  · rw [zipfPMF, if_neg hk]
    exact div_nonneg zero_le_one (le_of_lt hH)

#print axioms solution

