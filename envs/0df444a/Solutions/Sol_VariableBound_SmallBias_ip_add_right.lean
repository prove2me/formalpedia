-- Prove2me | solution 1 for VariableBound.SmallBias.ip_add_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:56:13.997127+00:00
-- url     : https://prove2.me/submissions/ccdb45af-9e73-42a3-8f5d-da4534f520c6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Definitions.Def_VariableBound_Family_SmallBias

set_option autoImplicit false
section
section
open VariableBound VariableBound.SmallBias
open Finset AppVariables
variable {s : ℕ}
namespace VariableBound.SmallBias
theorem _root_.solution (x y z : Fin s → ZMod 2) : ip x (y + z) = ip x y + ip x z := by
  simp [ip, mul_add, sum_add_distrib]
end VariableBound.SmallBias
