-- Prove2me | solution 1 for ThreeSum.TernaryBank.deficit_product_eq_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:35:19.543491+00:00
-- url     : https://prove2.me/submissions/ef33f839-ea91-4602-af8a-610654836dab

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
namespace ThreeSum.TernaryBank
theorem _root_.solution {N : ℕ} (Q : TritWord N) (z : ℝ) :
    (∏ i : Fin N, (if Q i = 0 then 1 else if Q i = 1 then 1 + z
      else 1 + z + z ^ 2)) =
    (1 + z) ^ digitCount Q 1 * (1 + z + z ^ 2) ^ digitCount Q 2 := by
  have hlocal (q : Fin 3) :
      (if q = 0 then 1 else if q = 1 then 1 + z else 1 + z + z ^ 2) =
        (1 + z) ^ (if q = 1 then 1 else 0 : ℕ) *
          (1 + z + z ^ 2) ^ (if q = 2 then 1 else 0 : ℕ) := by
    fin_cases q <;> norm_num [Fin.ext_iff]
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.prod_pow_eq_pow_sum]
  rfl
end ThreeSum.TernaryBank
