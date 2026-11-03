-- Prove2me | solution 1 for PlotkinShmoysTardos.weak_duality_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:26:27.482104+00:00
-- url     : https://prove2.me/submissions/18d35085-e76d-4b5a-a944-fa1bd67217e8

import Mathlib

open Finset Matrix

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (x : Fin n → ℝ) (hx : x ∈ P) (l : ℝ)
    (hfeas : ∀ i, A.mulVec x i ≤ b i + l * d i) (y : Fin m → ℝ) (hy : 0 ≤ y)
    (x' : Fin n → ℝ) (hx' : x' ∈ P)
    (hmin : ∀ z ∈ P, y ⬝ᵥ (A.mulVec x' - b) ≤ y ⬝ᵥ (A.mulVec z - b)) :
    y ⬝ᵥ (A.mulVec x - b) ≤ l * (y ⬝ᵥ d) ∧
      y ⬝ᵥ (A.mulVec x' - b) ≤ y ⬝ᵥ (A.mulVec x - b) ∧
      (0 < y ⬝ᵥ d → y ⬝ᵥ (A.mulVec x' - b) / (y ⬝ᵥ d) ≤ l) := by
  let _ := hx'
  have h1 : y ⬝ᵥ (A.mulVec x - b) ≤ l * (y ⬝ᵥ d) := by
    simp only [dotProduct, Pi.sub_apply, mul_sum]
    refine sum_le_sum fun i _ => ?_
    have hi : A.mulVec x i - b i ≤ l * d i := by linarith [hfeas i]
    have hyi : 0 ≤ y i := hy i
    nlinarith
  have h2 : y ⬝ᵥ (A.mulVec x' - b) ≤ y ⬝ᵥ (A.mulVec x - b) := hmin x hx
  refine ⟨h1, h2, fun hd_pos => ?_⟩
  rw [div_le_iff₀ hd_pos]
  exact h2.trans h1
