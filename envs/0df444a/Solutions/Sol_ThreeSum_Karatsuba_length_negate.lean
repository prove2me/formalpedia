-- Prove2me | solution 1 for ThreeSum.Karatsuba.length_negate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:21.630207+00:00
-- url     : https://prove2.me/submissions/e82c7f99-3f35-4069-bf3d-245ac3f486af

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Karatsuba
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
attribute [local simp] ThreeSum.Karatsuba.length_plus

set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.Karatsuba
theorem _root_.solution (as : List ℤ) : (negate as).length = as.length := by
  simp [negate]
end ThreeSum.Karatsuba
