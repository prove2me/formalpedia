-- Prove2me | solution 1 for ZipfLaw.zipfPMF_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:34:06.358907+00:00
-- url     : https://prove2.me/submissions/b5c77b72-539f-4b29-a290-7b35bcaf37d8

import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

private lemma zipf_harmonic_pos (N : ℕ) (hN : 1 ≤ N) (s : ℝ) : 0 < genHarmonic N s := by
  unfold genHarmonic
  exact Finset.sum_pos' (fun k _ => by positivity)
    ⟨1, by simp [hN], by norm_num⟩

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    ∑ k ∈ Finset.Icc 1 N, zipfPMF N s k = 1 := by
  have hH := zipf_harmonic_pos N hN s
  calc
    (∑ k ∈ Finset.Icc 1 N, zipfPMF N s k) =
        (∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) ^ s) / genHarmonic N s := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun k hk => by
        rw [zipfPMF, if_pos (Finset.mem_Icc.mp hk)])
    _ = 1 := div_self (ne_of_gt hH)

#print axioms solution

