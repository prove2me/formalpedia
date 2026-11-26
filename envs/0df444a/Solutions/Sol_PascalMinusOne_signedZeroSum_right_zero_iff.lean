-- Prove2me | solution 1 for PascalMinusOne.signedZeroSum_right_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:20:01.698293+00:00
-- url     : https://prove2.me/submissions/59379d67-cc8a-44d9-9173-35ed1c9e0410

import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Definitions.Def_PascalMinusOne_SignedTokens
import Theorems.Thm_PascalMinusOne_signedZeroSum_one_one
import Theorems.Thm_PascalMinusOne_signedZeroSum_m_zero
import Theorems.Thm_PascalMinusOne_signedZeroSum_zero_m
attribute [local simp] PascalMinusOne.signedZeroSum_one_one
attribute [local simp] PascalMinusOne.signedZeroSum_m_zero
attribute [local simp] PascalMinusOne.signedZeroSum_zero_m

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution (m A : ℕ) :
    SignedZeroSum m A 0 ↔ m ∣ A := by
  simp [SignedZeroSum, Int.natCast_dvd_natCast]
end PascalMinusOne
