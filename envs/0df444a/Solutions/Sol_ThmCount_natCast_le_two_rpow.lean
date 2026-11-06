-- Prove2me | solution 1 for ThmCount.natCast_le_two_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:06:10.767428+00:00
-- url     : https://prove2.me/submissions/68159607-cebc-4005-a54c-8d7f68fcb14e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_Arith
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Tactic
import Definitions.Def_ThmCount_Rates

set_option autoImplicit false
section
section
open ThmCount
namespace ThmCount
theorem _root_.solution (q : ℕ) : (q : ℝ) ≤ (2 : ℝ) ^ (q : ℝ) := by
  rw [Real.rpow_natCast]
  exact_mod_cast (Nat.lt_two_pow_self (n := q)).le
end ThmCount
