-- Prove2me | solution 1 for VariableBound.Pairwise.card_H
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:47:00.132071+00:00
-- url     : https://prove2.me/submissions/adb5c9fe-d376-4329-a465-82ae4fa9b83b

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
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha : a - 1 ≤ s) (E : Fin m) :
    2 ^ (a - 1) * #{p : F × F | H bits ϑ a p E} = Fintype.card F ^ 2 := by
  have h1 : ϑ E ≠ ϑ E + 1 := by simp
  have h2 : #{p : F × F | H bits ϑ a p E} = #(Z bits a ×ˢ (univ : Finset F)) := by
    rw [← card_pair_mem (ϑ E) (ϑ E + 1) h1 (Z bits a ×ˢ univ)]
    congr 1
    ext p
    simp [H, Z]
  rw [h2, card_product, card_univ, ← mul_assoc, card_Z bits a ha, sq]
end VariableBound.Pairwise
