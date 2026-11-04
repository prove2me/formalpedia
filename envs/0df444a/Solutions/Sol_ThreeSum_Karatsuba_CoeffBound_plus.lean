-- Prove2me | solution 1 for ThreeSum.Karatsuba.CoeffBound.plus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:38:53.858287+00:00
-- url     : https://prove2.me/submissions/28ef2ab9-87aa-44d0-ab3e-caa79587a84a

import Definitions.Def_Submission_ThreeSum_Karatsuba
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift


attribute [local simp] ThreeSum.Karatsuba.plus_getD

set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial
open scoped BigOperators
namespace ThreeSum.Karatsuba
namespace CoeffBound
theorem _root_.solution {as bs : List ℤ} {U V : ℤ}
    (ha : CoeffBound as U) (hb : CoeffBound bs V) : CoeffBound (plus as bs) (U + V) := by
  intro j
  rw [plus_getD]
  exact (abs_add_le _ _).trans (add_le_add (ha j) (hb j))
end CoeffBound
end ThreeSum.Karatsuba
