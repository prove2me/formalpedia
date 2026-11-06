-- Prove2me | solution 1 for ThmCount.sqrt_sqrt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:57:33.707777+00:00
-- url     : https://prove2.me/submissions/bd6f4b9f-db7e-41fd-a49e-efc6bc1a48ce

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
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) = x ^ ((1 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num
end ThmCount
