-- Prove2me | solution 1 for ZipfLaw.zipfMandelbrotPMF_hasSum_one
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:48:44.918707+00:00
-- url     : https://prove2.me/submissions/b7f23ce8-e924-4ae8-a3c2-34158df2e7b7

import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (q s : ℝ) (hq : 0 ≤ q) (hs : 1 < s) :
    HasSum (fun k : ℕ => zipfMandelbrotPMF q s k) 1 := by
  have hq1 : 0 < q + 1 := by linarith
  have habs (n : ℕ) : |(n : ℝ) + (q + 1)| = (n : ℝ) + (q + 1) :=
    abs_of_pos (by positivity)
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℝ) + (q + 1)) ^ s) := by
    simpa only [habs] using (Real.summable_one_div_nat_add_rpow (q + 1) s).mpr hs
  have hC : 0 < hurwitzZetaSeries s (q + 1) := by
    exact hsum.tsum_pos (fun n => by positivity) 0 (by positivity)
  have hscaled : HasSum
      (fun n : ℕ => (1 / ((n : ℝ) + (q + 1)) ^ s) / hurwitzZetaSeries s (q + 1)) 1 := by
    have hseries : HasSum (fun n : ℕ => 1 / ((n : ℝ) + (q + 1)) ^ s)
        (hurwitzZetaSeries s (q + 1)) := hsum.hasSum
    simpa only [div_self hC.ne'] using
      hseries.div_const (hurwitzZetaSeries s (q + 1))
  have hshift : HasSum (fun n : ℕ => zipfMandelbrotPMF q s (n + 1)) 1 := by
    convert hscaled using 1
    funext n
    rw [zipfMandelbrotPMF, if_pos (by omega)]
    push_cast
    rw [show (n : ℝ) + 1 + q = (n : ℝ) + (q + 1) by ring]
    ring
  have hz : zipfMandelbrotPMF q s 0 = 0 := by simp [zipfMandelbrotPMF]
  have hshift' : HasSum (fun n : ℕ => zipfMandelbrotPMF q s (n + 1))
      (1 - ∑ k ∈ Finset.range 1, zipfMandelbrotPMF q s k) := by
    simpa only [Finset.sum_range_one, hz, sub_zero] using hshift
  exact (hasSum_nat_add_iff' 1).mp hshift'

#print axioms solution
