-- Prove2me | solution 1 for YeIPA.MCP.slice_monotone_inequality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:21:19.325817+00:00
-- url     : https://prove2.me/submissions/33a210fc-2835-473e-863c-401760ffaa5a

import Mathlib
import Definitions.Def_YeIPA_MCP_HomogeneousModel

open Matrix
open YeIPA.MCP

theorem solution {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_cont : ContinuousOn f (posOrthant n)) (hf_mono : MonotoneOnPos f)
    (r : Fin n → ℝ) (θ₁ θ₂ : ℝ) (x₁ s₁ x₂ s₂ : Fin n → ℝ)
    (h₁ : (x₁, s₁) ∈ Spp f (θ₁ • r)) (h₂ : (x₂, s₂) ∈ Spp f (θ₂ • r)) :
    (θ₂ - θ₁) * (r ⬝ᵥ (x₂ - x₁)) ≤ (x₂ - x₁) ⬝ᵥ (s₂ - s₁) := by
  obtain ⟨hx1, _, hs1⟩ := h₁
  obtain ⟨hx2, _, hs2⟩ := h₂
  simp only at hx1 hx2 hs1 hs2
  have hm := hf_mono x₂ hx2 x₁ hx1
  have e : s₂ - s₁ = (f x₂ - f x₁) + (θ₂ - θ₁) • r := by
    rw [hs1, hs2, sub_smul]; abel
  rw [e, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm (x₂ - x₁) r]
  linarith
