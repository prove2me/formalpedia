-- Prove2me | solution 1 for ThreeSum.TernarySignedDigits.carryAt_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:36.067577+00:00
-- url     : https://prove2.me/submissions/65db72cd-78aa-4029-8912-9c1458e7118e

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedDigits
open Finset
open scoped BigOperators
namespace ThreeSum.TernarySignedDigits
theorem _root_.solution {b x y J j : ℕ} (hj : j ≤ J) :
    carryAt (canonicalCarry b x y J) j=(carryNat b x y j : ℤ) := by
  simp [carryAt,canonicalCarry,show j<J+1 by omega]
end ThreeSum.TernarySignedDigits
