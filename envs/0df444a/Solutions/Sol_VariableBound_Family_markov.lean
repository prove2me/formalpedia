-- Prove2me | solution 1 for VariableBound.Family.markov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:06:34.77025+00:00
-- url     : https://prove2.me/submissions/3655ff67-5161-4f98-bcc7-72885b2eedb1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Family_Pairwise
import Definitions.Def_VariableBound_Family_SmallBias
import Definitions.Def_VariableBound_Family_Main
import Theorems.Thm_VariableBound_Family_card_mem

set_option autoImplicit false
section
section
open VariableBound
open Finset AppVariables VariableBound.Pairwise
open VariableBound.Family
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
namespace VariableBound.Family
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (hm : 1 ≤ m) :
    16 * #{u : F × F × F × F | ¬ 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m} ≤ Fintype.card F ^ 4 := by
  have h1 : ∑ u : F × F × F × F, 2 ^ a * #(Gam bits ϑ a u) ≤ m * Fintype.card F ^ 4 := by
    have h2 : ∀ u : F × F × F × F, #(Gam bits ϑ a u) = ∑ E : Fin m, if E ∈ Gam bits ϑ a u then 1 else 0 := by
      intro u
      simp
    simp_rw [h2]
    rw [← mul_sum, sum_comm, mul_sum]
    simp_rw [← card_filter]
    refine (sum_le_sum fun E _ => card_mem bits ϑ a ha1 ha E).trans ?_
    simp
  have h3 : #{u : F × F × F × F | ¬ 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m} * (16 * m) ≤ ∑ u : F × F × F × F, 2 ^ a * #(Gam bits ϑ a u) := by
    rw [← smul_eq_mul, ← sum_const]
    refine (sum_le_sum fun u hu => ?_).trans (sum_le_sum_of_subset (subset_univ _))
    exact (not_le.1 (mem_filter.1 hu).2).le
  refine Nat.le_of_mul_le_mul_right ?_ hm
  calc 16 * #{u : F × F × F × F | ¬ 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m} * m
      = #{u : F × F × F × F | ¬ 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m} * (16 * m) := by ring
    _ ≤ m * Fintype.card F ^ 4 := h3.trans h1
    _ = Fintype.card F ^ 4 * m := by ring
end VariableBound.Family
