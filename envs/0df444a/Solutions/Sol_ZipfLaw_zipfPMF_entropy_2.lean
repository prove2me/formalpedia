-- Prove2me | solution 2 for ZipfLaw.zipfPMF_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:28:31.928772+00:00
-- url     : https://prove2.me/submissions/fba93766-f0a1-4bd6-8e51-513c6336dad9

import Theorems.Thm_ZipfLaw_log_zipfPMF_affine
import Theorems.Thm_ZipfLaw_zipfPMF_sum_eq_one
import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

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
        rw [log_zipfPMF_affine N s k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2]
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
  rw [hsum, hweighted, zipfPMF_sum_eq_one N hN s]
  ring

#print axioms solution
