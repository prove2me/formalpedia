-- Prove2me | solution 1 for WeakGoldbach.symmetric_vonMangoldt_off_diagonal_lower_bound_above_2e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:16:21.510545+00:00
-- url     : https://prove2.me/submissions/0f77c0d7-08cc-4458-9980-0a15b6e56993
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_symmetric_vonMangoldt_total_with_3_2_margin_above_2e18
import Theorems.Thm_WeakGoldbach_vonMangoldt_diagonal_small_above_2e18

open WeakGoldbach

theorem solution (m : Nat) (hm : 2 * 10 ^ 18 < m) :
    (5 / 4 : Real) * Finset.prod ((2 * m).primeFactors.filter (fun p => 2 < p)) (fun p => ((p : Real) - 1) / ((p : Real) - 2)) * (m : Real) <=
      Finset.sum ((Finset.range (m - 1)).erase 0) (fun t => (ArithmeticFunction.vonMangoldt (m - t) : Real) * (ArithmeticFunction.vonMangoldt (m + t) : Real)) := by
  let F : Nat -> Real := fun t => (ArithmeticFunction.vonMangoldt (m - t) : Real) * (ArithmeticFunction.vonMangoldt (m + t) : Real)
  have hzero : 0 ∈ Finset.range (m - 1) := by
    simp only [Finset.mem_range]
    omega
  have hsplit : F 0 + Finset.sum ((Finset.range (m - 1)).erase 0) F = Finset.sum (Finset.range (m - 1)) F := by
    exact Finset.add_sum_erase (a := 0) _ _ hzero
  have hdiag : F 0 = (ArithmeticFunction.vonMangoldt m : Real) ^ 2 := by
    simp [F, pow_two]
  have htotal := WeakGoldbach.symmetric_vonMangoldt_total_with_3_2_margin_above_2e18 m hm
  have hsmall := WeakGoldbach.vonMangoldt_diagonal_small_above_2e18 m hm
  change (3 / 2 : Real) * Finset.prod ((2 * m).primeFactors.filter (fun p => 2 < p)) (fun p => ((p : Real) - 1) / ((p : Real) - 2)) * (m : Real) <= Finset.sum (Finset.range (m - 1)) F at htotal
  rw [Eq.symm hsplit, hdiag] at htotal
  nlinarith [htotal, hsmall]
