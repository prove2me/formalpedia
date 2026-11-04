-- Prove2me | solution 1 for ThreeSum.Karatsuba.CoeffBound.of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:42.169816+00:00
-- url     : https://prove2.me/submissions/948357d4-31b0-47de-b1d5-a1bfcb941e5b

import Definitions.Def_Submission_ThreeSum_Karatsuba
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Submission_ThreeSum_KaratsubaBounds

set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial
open scoped BigOperators
namespace ThreeSum.Karatsuba
namespace CoeffBound
theorem _root_.solution {as : List ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hm : ∀ x ∈ as, |x| ≤ U) : CoeffBound as U := by
  intro j
  by_cases hj : j < as.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hm _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega), abs_zero]
    exact hU
end CoeffBound
end ThreeSum.Karatsuba
