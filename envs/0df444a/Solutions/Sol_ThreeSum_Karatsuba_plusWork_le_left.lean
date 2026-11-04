-- Prove2me | solution 1 for ThreeSum.Karatsuba.plusWork_le_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:07:32.793205+00:00
-- url     : https://prove2.me/submissions/d6d755ea-474f-4b2f-b7cf-9811b1be1ad2

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Karatsuba

set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.Karatsuba
theorem _root_.solution (as bs : List ℤ) : plusWork as bs ≤ 2 * as.length + 1 := by
  unfold plusWork
  omega
end ThreeSum.Karatsuba
