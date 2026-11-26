-- Prove2me | solution 1 for PascalMinusOne.mod_pow_succ_eq_mod_add_digitAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:18:49.462904+00:00
-- url     : https://prove2.me/submissions/53f1e5bc-11c4-4207-afec-1b495a4fea4a

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Kummer
import Theorems.Thm_PascalMinusOne_evenDigitSum_zero
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
import Theorems.Thm_PascalMinusOne_oddDigitSum_zero
import Theorems.Thm_PascalMinusOne_parityDigitSums_cons
import Theorems.Thm_PascalMinusOne_parityDigitSums_nil
attribute [local simp] PascalMinusOne.evenDigitSum_zero
attribute [local simp] PascalMinusOne.mem_admissibleIndices_iff
attribute [local simp] PascalMinusOne.oddDigitSum_zero
attribute [local simp] PascalMinusOne.parityDigitSums_cons
attribute [local simp] PascalMinusOne.parityDigitSums_nil



set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution (p x i : ℕ) :
    x % p ^ (i + 1) = x % p ^ i + p ^ i * digitAt p x i := by
  simpa [pow_succ, digitAt] using
    (Nat.mod_mul (a := p ^ i) (b := p) (x := x))
end PascalMinusOne
