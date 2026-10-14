-- Prove2me | solution 1 for ZipfLaw.zipfPMF_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:48:41.647267+00:00
-- url     : https://prove2.me/submissions/a8a95fec-a1cf-4f80-9b43-f22ecbb7d2b0

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

private lemma pmf_sum (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    ∑ k ∈ Finset.Icc 1 N, zipfPMF N s k = 1 := by
  have hH := zipf_harmonic_pos N hN s
  calc
    (∑ k ∈ Finset.Icc 1 N, zipfPMF N s k) =
        (∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) ^ s) / genHarmonic N s := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun k hk => by
        rw [zipfPMF, if_pos (Finset.mem_Icc.mp hk)])
    _ = 1 := div_self (ne_of_gt hH)

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    -(∑ k ∈ Finset.Icc 1 N, zipfPMF N s k * Real.log (zipfPMF N s k)) =
      s / genHarmonic N s * (∑ k ∈ Finset.Icc 1 N, Real.log k / (k : ℝ) ^ s) +
        Real.log (genHarmonic N s) := by
  have hsum :
      (∑ k ∈ Finset.Icc 1 N, zipfPMF N s k * Real.log (zipfPMF N s k)) =
        -s * (∑ k ∈ Finset.Icc 1 N, zipfPMF N s k * Real.log k) -
          Real.log (genHarmonic N s) * (∑ k ∈ Finset.Icc 1 N, zipfPMF N s k) := by
    calc
      _ = ∑ k ∈ Finset.Icc 1 N,
          ((-s) * (zipfPMF N s k * Real.log k) -
            Real.log (genHarmonic N s) * zipfPMF N s k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [log_term N s k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2]
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hweighted :
      (∑ k ∈ Finset.Icc 1 N, zipfPMF N s k * Real.log k) =
        (∑ k ∈ Finset.Icc 1 N, Real.log k / (k : ℝ) ^ s) / genHarmonic N s := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    rw [zipfPMF, if_pos (Finset.mem_Icc.mp hk)]
    ring
  rw [hsum, hweighted, pmf_sum N hN s]
  ring

#print axioms solution

