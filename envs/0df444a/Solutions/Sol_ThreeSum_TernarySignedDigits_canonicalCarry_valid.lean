-- Prove2me | solution 1 for ThreeSum.TernarySignedDigits.canonicalCarry_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:40:55.835344+00:00
-- url     : https://prove2.me/submissions/2399d629-ebca-4420-9556-41b347c5c653

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_terminal
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryAt_canonical
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedDigits
open Finset
open scoped BigOperators
namespace ThreeSum.TernarySignedDigits
theorem _root_.solution {b x y J : ℕ} (h : x+y < b^J) :
    ValidCarry (canonicalCarry b x y J) := by
  constructor
  · rw [carryAt_canonical (by omega),carryNat_zero]; rfl
  · rw [carryAt_canonical le_rfl,carryNat_terminal h]; rfl
end ThreeSum.TernarySignedDigits
