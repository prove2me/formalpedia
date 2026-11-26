-- Prove2me | solution 1 for PascalMinusOne.signedZeroSum_one_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:17:21.913384+00:00
-- url     : https://prove2.me/submissions/ef37fd9d-4a5f-4a62-95f0-c030cb113023

import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Definitions.Def_PascalMinusOne_SignedTokens

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution (m : ℕ) : SignedZeroSum m 1 1 := by
  simp [SignedZeroSum]
end PascalMinusOne
