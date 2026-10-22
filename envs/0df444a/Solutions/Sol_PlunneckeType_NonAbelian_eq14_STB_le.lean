-- Prove2me | solution 1 for PlunneckeType.NonAbelian.eq14_STB_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:14:03.745995+00:00
-- url     : https://prove2.me/submissions/788178cd-7a9a-4a4c-8dd5-dc2a217be863

import Mathlib
set_option autoImplicit false
open scoped Pointwise
open Finset

theorem solution {G : Type*} [Group G] [DecidableEq G] (A B S T : Finset G) (α β : ℝ)
    (hB : B.Nonempty)
    (h2 : ∀ b ∈ B, (#(A * {b} * B) : ℝ) ≤ β * #A)
    (hSA : S ⊆ A) (hTB : T ⊆ B) (hT : (#T : ℝ) ≤ α) :
    (#(S * T * B) : ℝ) ≤ α * β * #A := by
  have hsub : S * T * B ⊆ T.biUnion (fun t => A * {t} * B) := by
    intro x hx
    rw [mem_mul] at hx
    obtain ⟨y, hy, c, hc, rfl⟩ := hx
    rw [mem_mul] at hy
    obtain ⟨a, ha, t, ht, rfl⟩ := hy
    rw [mem_biUnion]
    exact ⟨t, ht, mem_mul.2 ⟨a * t, mem_mul.2 ⟨a, hSA ha, t, mem_singleton_self t, rfl⟩, c, hc, rfl⟩⟩
  obtain ⟨b₀, hb₀⟩ := hB
  have hβ : 0 ≤ β * #A := le_trans (Nat.cast_nonneg _) (h2 b₀ hb₀)
  have h1 : #(S * T * B) ≤ ∑ t ∈ T, #(A * {t} * B) :=
    (card_le_card hsub).trans card_biUnion_le
  have h2' : (#(S * T * B) : ℝ) ≤ ∑ t ∈ T, (#(A * {t} * B) : ℝ) := by exact_mod_cast h1
  have h3 : ∑ t ∈ T, (#(A * {t} * B) : ℝ) ≤ ∑ _t ∈ T, β * #A :=
    sum_le_sum (fun t ht => h2 t (hTB ht))
  rw [sum_const, nsmul_eq_mul] at h3
  calc (#(S * T * B) : ℝ) ≤ #T * (β * #A) := h2'.trans h3
    _ ≤ α * (β * #A) := mul_le_mul_of_nonneg_right hT hβ
    _ = α * β * #A := by ring
