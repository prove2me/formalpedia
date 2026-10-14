-- Prove2me | solution 1 for ZipfLaw.log_zipfPMF_affine
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:48:44.163166+00:00
-- url     : https://prove2.me/submissions/e26ddf91-5193-4c43-8239-79db0e336089

import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

private lemma zipf_harmonic_pos (N : ℕ) (hN : 1 ≤ N) (s : ℝ) : 0 < genHarmonic N s := by
  unfold genHarmonic
  exact Finset.sum_pos' (fun k _ => by positivity)
    ⟨1, by simp [hN], by norm_num⟩

private lemma log_term (N : ℕ) (s : ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Real.log (zipfPMF N s k) = -s * Real.log k - Real.log (genHarmonic N s) := by
  have hH := zipf_harmonic_pos N (le_trans hk1 hkN) s
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  have hp := Real.rpow_pos_of_pos hkpos s
  rw [zipfPMF, if_pos ⟨hk1, hkN⟩, Real.log_div (by positivity) hH.ne',
    Real.log_div (by norm_num) hp.ne', Real.log_one, Real.log_rpow hkpos]
  ring

theorem solution (N : ℕ) (s : ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Real.log (zipfPMF N s k) = -s * Real.log k - Real.log (genHarmonic N s) := by
  exact log_term N s k hk1 hkN

#print axioms solution

