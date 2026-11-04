-- Prove2me | solution 1 for ThreeSum.TernarySignedDigits.carryNat_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:37:01.578467+00:00
-- url     : https://prove2.me/submissions/18e11119-75e1-4830-9a9e-3d17fc88f537

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernarySignedDigits

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedDigits
open Finset
open scoped BigOperators
namespace ThreeSum.TernarySignedDigits
theorem _root_.solution (b x y : ℕ) : carryNat b x y 0=0 := by
  simp [carryNat,quotient]
end ThreeSum.TernarySignedDigits
