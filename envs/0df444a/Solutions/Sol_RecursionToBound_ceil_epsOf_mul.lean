-- Prove2me | solution 1 for RecursionToBound.ceil_epsOf_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:50:58.047522+00:00
-- url     : https://prove2.me/submissions/f185462c-0345-468d-b049-b87b3b587017

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

set_option autoImplicit false
section
section
open RecursionToBound
open Finset SparsificationLemma
namespace RecursionToBound
theorem _root_.solution (r : ℕ × ℕ) (n : ℕ) : ⌈epsOf r * (n : ℚ)⌉₊ = ceilDiv (min r.1 r.2 * n) r.2 := by
  have e : ((min r.1 r.2 : ℕ) : ℚ) * (n : ℚ) = ((min r.1 r.2 * n : ℕ) : ℚ) := by push_cast; ring
  rw [epsOf_eq, div_mul_eq_mul_div, e, ceil_natCast_div]
end RecursionToBound
