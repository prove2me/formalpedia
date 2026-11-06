-- Prove2me | solution 1 for RecursionToBound.logC_epsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:50:53.332194+00:00
-- url     : https://prove2.me/submissions/e52149f4-166c-46dd-a69e-16489472ea7f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Cert_Numbers
import Theorems.Thm_RecursionToBound_ceil_natCast_div
import Theorems.Thm_RecursionToBound_epsOf_eq
import Theorems.Thm_RecursionToBound_sqPred_cast

set_option autoImplicit false
section
section
open RecursionToBound
open Finset SparsificationLemma
namespace RecursionToBound
theorem _root_.solution (k : ℕ) (r : ℕ × ℕ) : Cal.logC k (epsOf r) = logN k r := by
  have e : (32 : ℚ) * ((sqPred k : ℕ) : ℚ) * (r.2 : ℚ) = ((32 * sqPred k * r.2 : ℕ) : ℚ) := by push_cast; ring
  rw [Cal.logC, Cal.xC, epsOf_eq, sqPred_cast, div_div_eq_mul_div, e, ceil_natCast_div, logN]
end RecursionToBound
