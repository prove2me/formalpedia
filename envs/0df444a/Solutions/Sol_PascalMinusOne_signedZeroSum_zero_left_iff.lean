-- Prove2me | solution 1 for PascalMinusOne.signedZeroSum_zero_left_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:20:06.472875+00:00
-- url     : https://prove2.me/submissions/0da76df1-5f44-42b4-afc4-05b0c2ceace4

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
theorem _root_.solution (m B : ℕ) :
    SignedZeroSum m 0 B ↔ m ∣ B := by
  simp [SignedZeroSum, Int.natCast_dvd_natCast]
end PascalMinusOne
