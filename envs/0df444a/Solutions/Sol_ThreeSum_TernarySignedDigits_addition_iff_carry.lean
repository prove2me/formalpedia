-- Prove2me | solution 1 for ThreeSum.TernarySignedDigits.addition_iff_carry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:42:59.8974+00:00
-- url     : https://prove2.me/submissions/06381b6f-4569-43d0-aafb-f91dc2824512

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Theorems.Thm_ThreeSum_TernarySignedDigits_addition_has_carry
import Theorems.Thm_ThreeSum_TernarySignedDigits_carry_implies_addition

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedDigits
open Finset
open scoped BigOperators
namespace ThreeSum.TernarySignedDigits
theorem _root_.solution {b J x y z : ℕ} (hx : x<b^J) (hy : y<b^J) (hz : z<b^J) :
    x+y=z ↔ ∃ c : CarryWord J, ValidCarry c ∧ DigitRelation b J x y z c := by
  constructor
  · exact fun h => addition_has_carry h hz
  · rintro ⟨c,hc,hd⟩
    exact carry_implies_addition hx hy hz hc hd
end ThreeSum.TernarySignedDigits
