-- Prove2me | solution 1 for ThreeSum.Auxiliary.missWeight_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:58.433557+00:00
-- url     : https://prove2.me/submissions/7d3b00ca-482a-4c7c-b354-0f84c6d6a480

import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Mathlib.RingTheory.Coprime.Lemmas
import Definitions.Def_Submission_ThreeSum_Auxiliary
import Theorems.Thm_ThreeSum_Auxiliary_separates_nonzero
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_pos_of_witness


set_option autoImplicit false
open ThreeSum ThreeSum.Auxiliary
open Finset
open scoped BigOperators
namespace ThreeSum.Auxiliary
theorem _root_.solution (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p)
    {M : ℕ} (hprod : M < ∏ p ∈ C, p)
    {z : ℤ} (hz : z ≠ 0) (hbound : z.natAbs ≤ M) :
    1 ≤ Arithmetic.missWeight (moduli C) z := by
  obtain ⟨p, hp, hpz⟩ := separates_nonzero C hC hprod hz hbound
  exact Arithmetic.missWeight_pos_of_witness hp hpz
end ThreeSum.Auxiliary
