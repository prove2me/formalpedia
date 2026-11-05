-- Prove2me | solution 1 for P2M_Groundwork_Grid_rowNet_sized__9b8262c1a57f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:16:57.047927+00:00
-- url     : https://prove2.me/submissions/339dd67c-6ac6-46ee-95ff-2eec441ac27b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_RowNet
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_Groundwork_Grid_Size
import Theorems.Thm_P2M_Groundwork_Grid_rowNet_shaped__a4d8a707e609
import Theorems.Thm_Groundwork_abs_prod_le_one
import Theorems.Thm_P2M_Groundwork_Grid_rowNet___43280a58588e
import Theorems.Thm_P2M_Groundwork_Network___comm_f75ed8fe8218

section
namespace Groundwork.Grid
open Finset
private theorem abs_boole_le (p : Prop) [Decidable p] : |if p then (1 : ℤ) else 0| ≤ 1 := by
  split_ifs <;> simp
private theorem abs_prod_le_pow {ι : Type} (s : Finset ι) (f : ι → ℤ) (B : ℕ) (h : ∀ i ∈ s, |f i| ≤ 2 ^ B) :
    |∏ i ∈ s, f i| ≤ 2 ^ (#s * B) := by
  calc |∏ i ∈ s, f i| = ∏ i ∈ s, |f i| := abs_prod _ _
    _ ≤ ∏ _i ∈ s, (2 : ℤ) ^ B := prod_le_prod (fun _ _ => abs_nonneg _) h
    _ = 2 ^ (#s * B) := by rw [prod_const, ← pow_mul, Nat.mul_comm]
private theorem abs_mul_prod_le {ι κ : Type} (s : Finset ι) (e : ι → ℤ) (t : Finset κ) (f : κ → ℤ) {b m : ℕ}
    (he : ∀ i, |e i| ≤ 1) (hf : ∀ k, |f k| ≤ 2 ^ b) (hm : #t * b ≤ m) :
    |(∏ i ∈ s, e i) * ∏ k ∈ t, f k| ≤ 2 ^ m := by
  rw [abs_mul]
  calc |∏ i ∈ s, e i| * |∏ k ∈ t, f k| ≤ 1 * 2 ^ (#t * b) :=
        mul_le_mul (abs_prod_le_one s e he) (abs_prod_le_pow t f b fun k _ => hf k) (abs_nonneg _) zero_le_one
    _ = 2 ^ (#t * b) := one_mul _
    _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
private theorem card_lt_le {g : ℕ} (X : Type) [Fintype X] [LinearOrder X] (hX : Fintype.card X = g) :
    #(univ.filter fun k : X × X => k.1 < k.2) ≤ g ^ 2 :=
  (card_le_univ _).trans_eq (by rw [Fintype.card_prod, hX, sq])
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
private theorem abs_rowNet_Ψ_lt {g L b m : ℕ} (hγ : Fintype.card γ = g) (R : Inst (ρ × γ) α)
    {G : Rect ρ γ → α → α → α → α → ℤ} (C : Rect ρ γ → Cut α τ) (t₀ : τ) (hF : ∀ ω, (C ω).Factors (G ω))
    (hG : ∀ ω x y u v, |G ω x y u v| ≤ 2 ^ b) (hm : g ^ 2 * b ≤ m) {a c : ρ} (h : a < c) (z z' : RowSt ρ γ α) :
    |(rowNet R C t₀ L).Ψ a c z z'| ≤ 2 ^ m := by
  rw [rowNet_Ψ hF R t₀ L h]
  exact abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => hG _ _ _ _ _)
    ((Nat.mul_le_mul_right _ (card_lt_le γ hγ)).trans hm)
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
theorem _root_.solution {g L m B b : ℕ} (hm : 1 ≤ m) (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g)
    (hα : Fintype.card α = 2 ^ L) (R : Inst (ρ × γ) α) (hR : ∀ w h, |R w h| ≤ 2 ^ B)
    {G : Rect ρ γ → α → α → α → α → ℤ} (C : Rect ρ γ → Cut α τ) (t₀ : τ)
    (hF : ∀ ω, (C ω).Factors (G ω)) (hcard : ∀ ω, #(C ω).lab ≤ 2 ^ (C ω).cap) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L)
    (htop : ∀ ω x y θ, |(C ω).top x y θ| ≤ 2 ^ b) (hbot : ∀ ω u v θ, |(C ω).bot u v θ| ≤ 2 ^ b)
    (hG : ∀ ω x y u v, |G ω x y u v| ≤ 2 ^ b) :
    (rowNet R C t₀ L).Sized (m * (g ^ 3 * L)) (g * B + g ^ 2 * b) where
  toShaped := rowNet_shaped' hm hρ hγ hα R C t₀ hcard hcap
  abs_W a z := by
    simp only [rowNet, rowW]
    rw [mul_comm]
    refine abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => hR _ _) ?_
    rw [Finset.card_univ, hγ]
    exact Nat.le_add_right _ _
  abs_f a c z θ := by
    have hm : #(univ.filter fun k : γ × γ => k.1 < k.2) * b ≤ g * B + g ^ 2 * b :=
      (Nat.mul_le_mul_right _ (card_lt_le γ hγ)).trans (Nat.le_add_left _ _)
    simp only [rowNet]
    split_ifs
    · exact abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => htop _ _ _ _) hm
    · exact abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => hbot _ _ _ _) hm
  abs_Ψ a c z z' hac := by
    rcases lt_or_gt_of_ne hac with h | h
    · exact abs_rowNet_Ψ_lt hγ R C t₀ hF hG (Nat.le_add_left _ _) h z z'
    · rw [Network.Ψ_comm]
      exact abs_rowNet_Ψ_lt hγ R C t₀ hF hG (Nat.le_add_left _ _) h z' z
end Groundwork.Grid
