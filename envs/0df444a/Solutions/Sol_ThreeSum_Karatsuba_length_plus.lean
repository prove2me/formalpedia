-- Prove2me | solution 1 for ThreeSum.Karatsuba.length_plus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:07:31.530419+00:00
-- url     : https://prove2.me/submissions/bc3eeaf3-7319-48b6-87cb-7aa483cec44d

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
theorem _root_.solution (as bs : List ℤ) :
    (plus as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [plus]
  | cons a as ih =>
    cases bs with
    | nil => simp [plus]
    | cons b bs => simpa [plus, Nat.succ_max_succ] using congrArg Nat.succ (ih bs)
end ThreeSum.Karatsuba
