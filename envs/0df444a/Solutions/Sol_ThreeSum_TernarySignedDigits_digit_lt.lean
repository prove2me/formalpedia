-- Prove2me | solution 1 for ThreeSum.TernarySignedDigits.digit_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:24:06.422174+00:00
-- url     : https://prove2.me/submissions/715eee2d-f610-40d0-9a70-94aae519841e

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
theorem _root_.solution {b : ℕ} (hb : 0 < b) (x j : ℕ) : digit b x j < b := Nat.mod_lt _ hb
end ThreeSum.TernarySignedDigits
