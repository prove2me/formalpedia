-- Prove2me | solution 1 for ZipfLaw.zipfPMF_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:48:43.312562+00:00
-- url     : https://prove2.me/submissions/3c7acdbf-6b1f-4a63-91e5-b299e653aa9f

import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

private lemma zipf_harmonic_pos (N : ℕ) (hN : 1 ≤ N) (s : ℝ) : 0 < genHarmonic N s := by
  unfold genHarmonic
  exact Finset.sum_pos' (fun k _ => by positivity)
    ⟨1, by simp [hN], by norm_num⟩

theorem solution (N : ℕ) (s : ℝ) (n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    zipfPMF N s 1 / zipfPMF N s n = (n : ℝ) ^ s := by
  have hN : 1 ≤ N := le_trans hn1 hnN
  have hH := zipf_harmonic_pos N hN s
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hp := Real.rpow_pos_of_pos hnpos s
  have h1 : zipfPMF N s 1 = 1 / genHarmonic N s := by simp [zipfPMF, hN]
  rw [h1, zipfPMF, if_pos ⟨hn1, hnN⟩]
  field_simp [ne_of_gt hH, ne_of_gt hp] <;> ring

#print axioms solution

