-- Prove2me | solution 1 for VariableBound.SmallBias.ip_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:03:25.699213+00:00
-- url     : https://prove2.me/submissions/12bb3ef5-ddce-44a8-ba64-8491de163f32

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
import Theorems.Thm_VariableBound_SmallBias_ip_half
import Theorems.Thm_VariableBound_SmallBias_ip_zero

set_option autoImplicit false
section
section
open VariableBound VariableBound.SmallBias
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] {s : ℕ}
namespace VariableBound.SmallBias
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (w : F) : 2 * #{u₄ : F | ip (bits w) (bits u₄) = 1} ≤ Fintype.card F := by
  rcases eq_or_ne w 0 with hw | hw
  · rw [hw, ip_zero]
    exact Nat.zero_le _
  · exact (ip_half bits w hw).le
end VariableBound.SmallBias
