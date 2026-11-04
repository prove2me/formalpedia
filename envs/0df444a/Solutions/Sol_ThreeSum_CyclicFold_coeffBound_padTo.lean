-- Prove2me | solution 1 for ThreeSum.CyclicFold.coeffBound_padTo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:41:38.865439+00:00
-- url     : https://prove2.me/submissions/886052c6-f863-433a-a268-c03b81a8194e

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_padTo
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff



set_option autoImplicit false
open ThreeSum ThreeSum.CyclicFold
open Finset Polynomial Karatsuba
open scoped BigOperators
namespace ThreeSum.CyclicFold
theorem _root_.solution {as : List ℤ} {U : ℤ} (h : CoeffBound as U) (n : ℕ) :
    CoeffBound (padTo n as) U := by
  intro j
  rw [← asPolynomial_coeff, asPolynomial_padTo, asPolynomial_coeff]
  exact h j
end ThreeSum.CyclicFold
