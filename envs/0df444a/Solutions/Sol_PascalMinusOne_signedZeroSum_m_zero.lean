-- Prove2me | solution 1 for PascalMinusOne.signedZeroSum_m_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:18:05.792675+00:00
-- url     : https://prove2.me/submissions/5cbc2006-deb1-4812-8b7b-aa447a542155

import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Definitions.Def_PascalMinusOne_SignedTokens
import Theorems.Thm_PascalMinusOne_signedZeroSum_one_one
attribute [local simp] PascalMinusOne.signedZeroSum_one_one

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution (m : ℕ) : SignedZeroSum m m 0 := by
  simp [SignedZeroSum]
end PascalMinusOne
