-- Prove2me | solution 1 for ThmVariables.cutNumber_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:18:03.765081+00:00
-- url     : https://prove2.me/submissions/0d2c8f3b-024e-4204-823e-7b48f4a5546a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_ThmVariables_Bound
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ThmVariables_PartA

set_option autoImplicit false
section
section
open ThmVariables
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms
open Sat3 (CNF)
namespace ThmVariables
theorem _root_.solution (K : ℕ → ℕ) (num : List Unit × List Unit → ℕ × ℕ) (l : ℕ) : 0 ≤ cutNumber K num l := le_min (by positivity) zero_le_one
end ThmVariables
