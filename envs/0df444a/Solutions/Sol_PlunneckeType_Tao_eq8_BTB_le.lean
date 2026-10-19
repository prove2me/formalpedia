-- Prove2me | solution 1 for PlunneckeType.Tao.eq8_BTB_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:39:20.883644+00:00
-- url     : https://prove2.me/submissions/feab8e2e-0395-41e2-8d58-570f9c02efba

import Mathlib
set_option autoImplicit false
open scoped Pointwise
open Finset

theorem solution {G : Type*} [Group G] [DecidableEq G] (B T : Finset G) (α β : ℝ)
    (hBbB : ∀ b ∈ B, (#(B * {b} * B) : ℝ) ≤ β * #B)
    (hTB : T ⊆ B) (hT : (#T : ℝ) ≤ α) :
    (#(B * T * B) : ℝ) ≤ α * β * #B := by
  have hsub : B * T * B ⊆ T.biUnion (fun t => B * {t} * B) := by
    intro x hx
    rw [mem_mul] at hx
    obtain ⟨y, hy, c, hc, rfl⟩ := hx
    rw [mem_mul] at hy
    obtain ⟨a, ha, t, ht, rfl⟩ := hy
    rw [mem_biUnion]
    exact ⟨t, ht, mem_mul.2 ⟨a * t, mem_mul.2 ⟨a, ha, t, mem_singleton_self t, rfl⟩, c, hc, rfl⟩⟩
  rcases B.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
  · simp
  · have hβ : 0 ≤ β * #B := le_trans (Nat.cast_nonneg _) (hBbB b₀ hb₀)
    have h1 : #(B * T * B) ≤ ∑ t ∈ T, #(B * {t} * B) :=
      (card_le_card hsub).trans card_biUnion_le
    have h2 : (#(B * T * B) : ℝ) ≤ ∑ t ∈ T, (#(B * {t} * B) : ℝ) := by exact_mod_cast h1
    have h3 : ∑ t ∈ T, (#(B * {t} * B) : ℝ) ≤ ∑ _t ∈ T, β * #B :=
      sum_le_sum (fun t ht => hBbB t (hTB ht))
    rw [sum_const, nsmul_eq_mul] at h3
    calc (#(B * T * B) : ℝ) ≤ #T * (β * #B) := h2.trans h3
      _ ≤ α * (β * #B) := mul_le_mul_of_nonneg_right hT hβ
      _ = α * β * #B := by ring
