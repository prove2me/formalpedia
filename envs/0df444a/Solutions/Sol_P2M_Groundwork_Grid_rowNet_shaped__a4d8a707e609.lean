-- Prove2me | solution 1 for P2M_Groundwork_Grid_rowNet_shaped__a4d8a707e609
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:15:01.646393+00:00
-- url     : https://prove2.me/submissions/5c6e9cfb-a6e4-442e-969b-49903c1f7ebe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_RowNet
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_Groundwork_Grid_Size
import Theorems.Thm_Groundwork_Grid_rowNet_c_le
import Theorems.Thm_Groundwork_card_tuples

section
namespace Groundwork.Grid
open Finset
private theorem sum_le_card_mul {ι : Type} (s : Finset ι) (f : ι → ℕ) (c : ℕ) (h : ∀ i ∈ s, f i ≤ c) :
    ∑ i ∈ s, f i ≤ #s * c :=
  (Finset.sum_le_sum h).trans (Finset.sum_const_nat fun _ _ => rfl).le
private theorem sum_erase_le {g c : ℕ} (X : Type) [Fintype X] [DecidableEq X] (hX : Fintype.card X = g) (F : X → ℕ)
    (hF : ∀ b, F b ≤ g ^ 2 * c) (a : X) : ∑ b ∈ univ.erase a, F b ≤ g ^ 3 * c := by
  refine (sum_le_card_mul _ _ _ fun b _ => hF b).trans ?_
  rw [Finset.card_erase_of_mem (mem_univ a), Finset.card_univ, hX, ← Nat.mul_assoc]
  refine Nat.mul_le_mul_right _ ?_
  calc (g - 1) * g ^ 2 ≤ g * g ^ 2 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = g ^ 3 := by ring
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [DecidableEq α] in
/-- A row has g·g² half-edges. -/
private theorem card_state {g L : ℕ} (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g) (hα : Fintype.card α = 2 ^ L) :
    Fintype.card (RowSt ρ γ α) = 2 ^ (g ^ 3 * L) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_prod, hα, hρ, hγ, ← pow_mul, ← pow_mul]
  congr 1
  ring
omit [DecidableEq α] in
/-- The number of labels of two rows. -/
private theorem card_labels_le {g L : ℕ} (hγ : Fintype.card γ = g) (hα : Fintype.card α = 2 ^ L)
    (S : γ × γ → Finset τ) (e : γ × γ → ℕ) (h : ∀ k, #(S k) ≤ 2 ^ e k) (t₀ : τ) :
    #((univ : Finset (γ → α)) ×ˢ tuples (fun k : γ × γ => k.1 < k.2) S t₀) ≤
      2 ^ (g * L + ∑ k : γ × γ with k.1 < k.2, e k) := by
  rw [card_product, card_univ, Fintype.card_fun, hα, hγ, ← pow_mul, card_tuples, pow_add, ← prod_pow_eq_pow_sum,
    Nat.mul_comm L g]
  exact Nat.mul_le_mul_left _ (prod_le_prod (fun _ _ => Nat.zero_le _) fun k _ => h k)
omit [Fintype α] [DecidableEq α]
end Groundwork.Grid
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution {g L m : ℕ} (hm : 1 ≤ m) (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g)
    (hα : Fintype.card α = 2 ^ L) (R : Inst (ρ × γ) α) (C : Rect ρ γ → Cut α τ) (t₀ : τ)
    (hcard : ∀ ω, #(C ω).lab ≤ 2 ^ (C ω).cap) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L) :
    (rowNet R C t₀ L).Shaped (m * (g ^ 3 * L)) where
  card_S a := by
    simp only [rowNet, Finset.card_univ]
    rw [card_state hρ hγ hα]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ hm)
  c_symm a b := by simp only [rowNet, min_comm, max_comm]
  sum_c a := by
    rw [Nat.mul_left_comm]
    exact sum_erase_le ρ hρ _ (fun b => rowNet_c_le hm hγ R C t₀ hcap a b) a
  card_lab a b hab := by
    simp only [Network.lab, rowNet, if_pos (min_lt_max.2 hab), rowΘ, hγ]
    exact card_labels_le hγ hα _ _ (fun k => hcard _) t₀
end Groundwork.Grid
