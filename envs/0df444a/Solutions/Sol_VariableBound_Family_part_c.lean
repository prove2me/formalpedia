-- Prove2me | solution 1 for VariableBound.Family.part_c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:07:16.153795+00:00
-- url     : https://prove2.me/submissions/6a4aae77-8bf6-4858-a067-e6e6df1db4ae

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Family_Pairwise
import Definitions.Def_VariableBound_Family_SmallBias
import Definitions.Def_VariableBound_Family_Main
import Theorems.Thm_VariableBound_Family_card_odd
import Theorems.Thm_VariableBound_Family_markov
import Theorems.Thm_VariableBound_Family_card_Om_add

set_option autoImplicit false
section
section
open VariableBound
open Finset AppVariables VariableBound.Pairwise
open VariableBound.Family
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
namespace VariableBound.Family
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (hm : 1 ≤ m) (h16 : 16 * m ≤ 2 ^ s)
    (V : Finset (Fin m)) (hV : 2 ^ a < #V) :
    #(Om bits ϑ a) ≤ 4 * #{u ∈ Om bits ϑ a | Odd #(Gam bits ϑ a u ∩ V)} := by
  have h1 := card_odd bits ϑ a ha1 ha h16 V hV
  have h2 : #{u : F × F × F × F | Odd #(Gam bits ϑ a u ∩ V)}
      ≤ #{u ∈ Om bits ϑ a | Odd #(Gam bits ϑ a u ∩ V)} + #{u : F × F × F × F | ¬ 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m} := by
    rw [← card_filter_add_card_filter_not (s := {u : F × F × F × F | Odd #(Gam bits ϑ a u ∩ V)}) fun u => 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m]
    refine Nat.add_le_add (card_le_card fun u hu => ?_) (card_le_card fun u hu => ?_)
    · simp only [mem_filter, mem_univ, true_and, Om] at hu ⊢
      exact ⟨hu.2, hu.1⟩
    · simp only [mem_filter, mem_univ, true_and] at hu ⊢
      exact hu.2
  have h3 := markov bits ϑ a ha1 ha hm
  have h4 := card_Om_add bits ϑ a
  omega
end VariableBound.Family
