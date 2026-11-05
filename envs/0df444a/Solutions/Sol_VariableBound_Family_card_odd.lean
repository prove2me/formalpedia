-- Prove2me | solution 1 for VariableBound.Family.card_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:05:48.867547+00:00
-- url     : https://prove2.me/submissions/edf67b86-737a-49f1-a7e8-a87a49e0d182

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Family_Pairwise
import Definitions.Def_VariableBound_Family_SmallBias
import Definitions.Def_VariableBound_Family_Main
import Theorems.Thm_VariableBound_Family_card_quad
import Theorems.Thm_VariableBound_Family_mem_Gam
import Theorems.Thm_VariableBound_Pairwise_second_moment
import Theorems.Thm_VariableBound_SmallBias_small_bias


set_option autoImplicit false
section
section
open VariableBound
open Finset AppVariables VariableBound.Pairwise
open VariableBound.Family
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
namespace VariableBound.Family
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (h16 : 16 * m ≤ 2 ^ s)
    (V : Finset (Fin m)) (hV : 2 ^ a < #V) :
    5 * Fintype.card F ^ 4 ≤ 16 * #{u : F × F × F × F | Odd #(Gam bits ϑ a u ∩ V)} := by
  have h1 : ∀ u : F × F × F × F, Gam bits ϑ a u ∩ V
      = {E ∈ {E ∈ V | H bits ϑ a (u.1, u.2.1) E} | ip (bits ((u.2.2.1, u.2.2.2).1 ^ E.val)) (bits (u.2.2.1, u.2.2.2).2) = 1} := by
    intro u
    ext E
    rw [mem_inter, mem_Gam, mem_filter, mem_filter]
    tauto
  simp_rw [h1]
  rw [card_quad fun p r => Odd #{E ∈ {E ∈ V | H bits ϑ a p E} | ip (bits (r.1 ^ E.val)) (bits r.2) = 1}]
  have h2 := second_moment bits ϑ a ha1 ha V hV
  set A : Finset (F × F) := {p : F × F | ∃ E ∈ V, H bits ϑ a p E} with hA
  have h3 : #A * (15 * Fintype.card F ^ 2)
      ≤ 32 * ∑ p : F × F, #{r : F × F | Odd #{E ∈ {E ∈ V | H bits ϑ a p E} | ip (bits (r.1 ^ E.val)) (bits r.2) = 1}} := by
    rw [mul_sum, ← smul_eq_mul, ← sum_const]
    refine (sum_le_sum fun p hp => SmallBias.small_bias bits h16 {E ∈ V | H bits ϑ a p E} ?_).trans (sum_le_sum_of_subset (subset_univ A))
    obtain ⟨E, hE, hH⟩ := (mem_filter.1 hp).2
    exact ⟨E, mem_filter.2 ⟨hE, hH⟩⟩
  generalize (∑ p : F × F, #{r : F × F | Odd #{E ∈ {E ∈ V | H bits ϑ a p E} | ip (bits (r.1 ^ E.val)) (bits r.2) = 1}}) = N at *
  have h4 : 2 * Fintype.card F ^ 2 * (15 * Fintype.card F ^ 2) ≤ 3 * #A * (15 * Fintype.card F ^ 2) := Nat.mul_le_mul_right _ h2.le
  have h5 : Fintype.card F ^ 4 = Fintype.card F ^ 2 * Fintype.card F ^ 2 := by ring
  rw [h5]
  generalize Fintype.card F ^ 2 = Q at *
  generalize hQQ : Q * Q = QQ at *
  have h6 : 2 * Q * (15 * Q) = 30 * QQ := by rw [← hQQ]; ring
  have h7 : 3 * #A * (15 * Q) = 3 * (#A * (15 * Q)) := by ring
  omega
end VariableBound.Family
