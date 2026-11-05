-- Prove2me | solution 1 for VariableBound.Pairwise.card_H_and
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:48:40.267342+00:00
-- url     : https://prove2.me/submissions/401b9362-2b66-41d1-bf79-1e3578467a0b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_VariableBound_Family_Pairwise
import Theorems.Thm_VariableBound_Pairwise_card_Z
import Theorems.Thm_VariableBound_Pairwise_card_pair_mem

set_option autoImplicit false
section
section
open VariableBound VariableBound.Pairwise
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
namespace VariableBound.Pairwise
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha : a - 1 ≤ s) (E E' : Fin m) (hE : E ≠ E') :
    4 ^ (a - 1) * #{p : F × F | H bits ϑ a p E ∧ H bits ϑ a p E'} = Fintype.card F ^ 2 := by
  have h1 : ϑ E ≠ ϑ E' := fun h => hE (ϑ.injective h)
  have h2 : #{p : F × F | H bits ϑ a p E ∧ H bits ϑ a p E'} = #(Z bits a ×ˢ Z bits a) := by
    rw [← card_pair_mem (ϑ E) (ϑ E') h1 (Z bits a ×ˢ Z bits a)]
    congr 1
    ext p
    simp [H, Z]
  rw [h2, card_product, ← card_Z bits a ha, show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  ring
end VariableBound.Pairwise
