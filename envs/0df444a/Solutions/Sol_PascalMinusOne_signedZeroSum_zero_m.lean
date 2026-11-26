-- Prove2me | solution 1 for PascalMinusOne.signedZeroSum_zero_m
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:18:56.134436+00:00
-- url     : https://prove2.me/submissions/bb924981-0dab-47b4-ae83-ea8d53e32278

import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Definitions.Def_PascalMinusOne_SignedTokens
import Theorems.Thm_PascalMinusOne_signedZeroSum_one_one
import Theorems.Thm_PascalMinusOne_signedZeroSum_m_zero
attribute [local simp] PascalMinusOne.signedZeroSum_one_one
attribute [local simp] PascalMinusOne.signedZeroSum_m_zero

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution (m : ℕ) : SignedZeroSum m 0 m := by
  simp [SignedZeroSum]
end PascalMinusOne
