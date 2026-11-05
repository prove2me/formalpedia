-- Prove2me | solution 1 for VariableBound.SmallBias.sum_ip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:57:35.37493+00:00
-- url     : https://prove2.me/submissions/a27135b1-6609-4411-9c2a-6f1506ce8716

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
import Theorems.Thm_VariableBound_SmallBias_ip_sum_left

set_option autoImplicit false
section
section
open VariableBound VariableBound.SmallBias
open Finset AppVariables
variable {F : Type} [Field F] [Algebra (ZMod 2) F] {m s : ℕ}
namespace VariableBound.SmallBias
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (V' : Finset (Fin m)) (u₃ u₄ : F) :
    ∑ E ∈ V', ip (bits (u₃ ^ E.val)) (bits u₄) = ip (bits (∑ E ∈ V', u₃ ^ E.val)) (bits u₄) := by
  rw [map_sum, ip_sum_left]
end VariableBound.SmallBias
