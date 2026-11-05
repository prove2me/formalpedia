-- Prove2me | solution 1 for VariableBound.SmallBias.ip_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:56:49.642458+00:00
-- url     : https://prove2.me/submissions/808efa27-8a44-4a7a-acaa-a5352d186edb

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
theorem _root_.solution {ι : Type} (T : Finset ι) (f : ι → Fin s → ZMod 2) (y : Fin s → ZMod 2) : ip (∑ e ∈ T, f e) y = ∑ e ∈ T, ip (f e) y := by
  simp only [ip, Finset.sum_apply, sum_mul]
  exact sum_comm
end VariableBound.SmallBias
