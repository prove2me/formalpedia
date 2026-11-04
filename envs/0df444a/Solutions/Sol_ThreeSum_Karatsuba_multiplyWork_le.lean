-- Prove2me | solution 1 for ThreeSum.Karatsuba.multiplyWork_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:49.017179+00:00
-- url     : https://prove2.me/submissions/a3dbec78-2e9c-40fd-80f4-280c09676fbb

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Karatsuba
import Theorems.Thm_ThreeSum_Karatsuba_multiplyWork_bound

set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.Karatsuba
theorem _root_.solution (k : ℕ) (as bs : List ℤ) :
    multiplyWork k as bs ≤ 83 * 3 ^ k := by
  have h := multiplyWork_bound k as bs
  omega
end ThreeSum.Karatsuba
