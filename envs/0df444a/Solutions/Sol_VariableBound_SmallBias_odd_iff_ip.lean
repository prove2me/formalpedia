-- Prove2me | solution 1 for VariableBound.SmallBias.odd_iff_ip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:58:15.137214+00:00
-- url     : https://prove2.me/submissions/82f18db1-f9cb-4405-8f74-3e65bbcdb88e

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
import Theorems.Thm_VariableBound_SmallBias_odd_iff
import Theorems.Thm_VariableBound_SmallBias_sum_ip

set_option autoImplicit false
section
section
open VariableBound VariableBound.SmallBias
open Finset AppVariables
variable {F : Type} [Field F] [Algebra (ZMod 2) F] {m s : ℕ}
namespace VariableBound.SmallBias
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (V' : Finset (Fin m)) (u₃ u₄ : F) :
    Odd #{E ∈ V' | ip (bits (u₃ ^ E.val)) (bits u₄) = 1} ↔ ip (bits (∑ E ∈ V', u₃ ^ E.val)) (bits u₄) = 1 := by
  rw [odd_iff, sum_ip]
end VariableBound.SmallBias
