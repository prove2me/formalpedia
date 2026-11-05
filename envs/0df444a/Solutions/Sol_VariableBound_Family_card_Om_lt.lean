-- Prove2me | solution 1 for VariableBound.Family.card_Om_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:06:45.557189+00:00
-- url     : https://prove2.me/submissions/7e77c3bd-86c6-4dd9-9cb6-890ff0d65b8f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Family_Pairwise
import Definitions.Def_VariableBound_Family_SmallBias
import Definitions.Def_VariableBound_Family_Main
import Theorems.Thm_VariableBound_Family_card_Om_add
import Theorems.Thm_VariableBound_Pairwise_card_F


set_option autoImplicit false
section
section
open VariableBound
open Finset AppVariables VariableBound.Pairwise
open VariableBound.Family
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
omit [DecidableEq F]
namespace VariableBound.Family
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (h32 : 2 ^ s < 32 * m) : #(Om bits ϑ a) < (32 * m) ^ 4 :=
  calc #(Om bits ϑ a) ≤ Fintype.card F ^ 4 := (Nat.le_add_right _ _).trans_eq (card_Om_add bits ϑ a)
    _ = (2 ^ s) ^ 4 := by rw [card_F bits]
    _ < (32 * m) ^ 4 := Nat.pow_lt_pow_left h32 (by norm_num)
end VariableBound.Family
