-- Prove2me | solution 1 for ThreeSum.Auxiliary.separates_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:25.598029+00:00
-- url     : https://prove2.me/submissions/e3113e59-6363-4142-8a27-fb292def44c1

import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Mathlib.RingTheory.Coprime.Lemmas
import Definitions.Def_Submission_ThreeSum_Auxiliary
import Theorems.Thm_ThreeSum_Auxiliary_moduli_product
import Theorems.Thm_ThreeSum_Auxiliary_moduli_pairwise_coprime
import Theorems.Thm_ThreeSum_Arithmetic_exists_aux_not_dvd_of_prod_bound


set_option autoImplicit false
open ThreeSum ThreeSum.Auxiliary
open Finset
open scoped BigOperators
namespace ThreeSum.Auxiliary
theorem _root_.solution (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p)
    {M : ℕ} (hprod : M < ∏ p ∈ C, p)
    {z : ℤ} (hz : z ≠ 0) (hbound : z.natAbs ≤ M) :
    ∃ p ∈ moduli C, ¬p ∣ z := by
  apply Arithmetic.exists_aux_not_dvd_of_prod_bound (moduli C) z
    (moduli_pairwise_coprime C hC) hz
  rw [moduli_product, Int.natAbs_natCast]
  exact hbound.trans_lt hprod
end ThreeSum.Auxiliary
