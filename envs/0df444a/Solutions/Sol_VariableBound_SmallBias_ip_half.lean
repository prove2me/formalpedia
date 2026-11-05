-- Prove2me | solution 1 for VariableBound.SmallBias.ip_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:58:12.562743+00:00
-- url     : https://prove2.me/submissions/0c3eab57-0c38-48d6-86fe-e55f70aa5ce9

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
import Theorems.Thm_VariableBound_SmallBias_half_strings

set_option autoImplicit false
section
section
open VariableBound VariableBound.SmallBias
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] {s : ℕ}
namespace VariableBound.SmallBias
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (w : F) (hw : w ≠ 0) : 2 * #{u₄ : F | ip (bits w) (bits u₄) = 1} = Fintype.card F := by
  have hx : bits w ≠ 0 := fun h => hw (bits.map_eq_zero_iff.mp h)
  have hc : #{u₄ : F | ip (bits w) (bits u₄) = 1} = #{y : Fin s → ZMod 2 | ip (bits w) y = 1} :=
    card_equiv bits.toEquiv fun u => by simp
  rw [hc, half_strings _ hx, Fintype.card_congr bits.toEquiv]
end VariableBound.SmallBias
