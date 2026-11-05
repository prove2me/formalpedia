-- Prove2me | solution 1 for ThmCount.one_le_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:23:51.758024+00:00
-- url     : https://prove2.me/submissions/acf95e26-e3c8-4227-b44b-1425fb4bdd32

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
theorem _root_.solution {x : ℝ} (hx : 2 ≤ x) : 1 ≤ Real.logb 2 x := by
  have h := Real.logb_le_logb_of_le one_lt_two two_pos hx
  rwa [Real.logb_self_eq_one one_lt_two] at h
end ThmCount
