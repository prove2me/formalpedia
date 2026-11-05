-- Prove2me | solution 1 for VariableBound.Family.part_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:07:50.56397+00:00
-- url     : https://prove2.me/submissions/7f5d4d16-a127-4a5a-8263-a0598074b0ba

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Family_Pairwise
import Definitions.Def_VariableBound_Family_SmallBias
import Definitions.Def_VariableBound_Family_Main
import Theorems.Thm_VariableBound_Family_card_mem
import Theorems.Thm_VariableBound_Family_card_Om

set_option autoImplicit false
section
section
open VariableBound
open Finset AppVariables VariableBound.Pairwise
open VariableBound.Family
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
namespace VariableBound.Family
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (hm : 1 ≤ m) (E : Fin m) :
    15 * 2 ^ a * #{u ∈ Om bits ϑ a | E ∈ Gam bits ϑ a u} ≤ 16 * #(Om bits ϑ a) := by
  have h : #{u ∈ Om bits ϑ a | E ∈ Gam bits ϑ a u} ≤ #{u : F × F × F × F | E ∈ Gam bits ϑ a u} :=
    card_le_card (filter_subset_filter _ (subset_univ _))
  calc 15 * 2 ^ a * #{u ∈ Om bits ϑ a | E ∈ Gam bits ϑ a u} = 15 * (2 ^ a * #{u ∈ Om bits ϑ a | E ∈ Gam bits ϑ a u}) := by ring
    _ ≤ 15 * (2 ^ a * #{u : F × F × F × F | E ∈ Gam bits ϑ a u}) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h)
    _ ≤ 15 * Fintype.card F ^ 4 := Nat.mul_le_mul_left _ (card_mem bits ϑ a ha1 ha E)
    _ ≤ 16 * #(Om bits ϑ a) := card_Om bits ϑ a ha1 ha hm
end VariableBound.Family
