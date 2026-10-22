-- Prove2me | solution 1 for SelfDualLP.Regularity.equation_9
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:26:19.830224+00:00
-- url     : https://prove2.me/submissions/e82597fb-7bbf-4a7c-a335-484955cbc9ae

import Mathlib
import Definitions.Def_SelfDualLP_Regularity_HLP

set_option autoImplicit false
open Matrix SelfDualLP.Regularity

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (w : HLPPoint m n)
    (hw : HLPFeasible A b c (fun _ => 1) (fun _ => 0) (fun _ => 1) w) :
    (∑ j, w.x j) + (∑ j, w.s j) + w.τ + w.κ -
      ((n : ℝ) + 1) * w.θ = (n : ℝ) + 1 := by
  obtain ⟨-, h2, h3, h4, -⟩ := hw
  have h0 : Aᵀ *ᵥ (fun _ => (0 : ℝ)) = 0 := by
    ext j; simp [Matrix.mulVec, dotProduct]
  have hAy : ∑ j, (Aᵀ *ᵥ w.y) j = (A *ᵥ fun _ => (1 : ℝ)) ⬝ᵥ w.y := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_one]
    rw [Finset.sum_comm]
    simp [Finset.sum_mul, mul_comm]
  have hs : ∑ j, w.s j = - ((A *ᵥ fun _ => (1 : ℝ)) ⬝ᵥ w.y) + w.τ * ∑ j, c j
      - w.θ * (∑ j, c j - n) := by
    have : ∀ j, w.s j = -(Aᵀ *ᵥ w.y) j + w.τ * c j - w.θ * (c j - 1) := by
      intro j
      rw [h2]
      simp [cBar, h0]
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      ← Finset.mul_sum, hAy, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  have hb : bBar A b (fun _ => (1 : ℝ)) ⬝ᵥ w.y = b ⬝ᵥ w.y - (A *ᵥ fun _ => (1 : ℝ)) ⬝ᵥ w.y := by
    simp [bBar, sub_dotProduct]
  have hcx : cBar A c (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) ⬝ᵥ w.x = c ⬝ᵥ w.x - ∑ j, w.x j := by
    simp [cBar, h0, sub_dotProduct, dotProduct, sub_mul, Finset.sum_sub_distrib]
  have hz : zBar b c (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) = ∑ j, c j + 1 := by
    simp [zBar, dotProduct]
  have hxs : ((fun _ => (1 : ℝ)) : Fin n → ℝ) ⬝ᵥ (fun _ => (1 : ℝ)) = n := by
    simp [dotProduct]
  rw [hb, hcx, hz, hxs] at h4
  rw [hz] at h3
  rw [hs]
  rw [h3]
  have hbd : b ⬝ᵥ w.y = b ⬝ᵥ w.y := rfl
  linear_combination (-1 : ℝ) * h4
