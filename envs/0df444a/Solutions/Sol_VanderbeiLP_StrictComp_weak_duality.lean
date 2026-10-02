-- Prove2me | solution 1 for VanderbeiLP.StrictComp.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:41:04.319708+00:00
-- url     : https://prove2.me/submissions/42d42f35-8970-4961-b280-70e5352df78d

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_PrimalDualPair

open Matrix

open VanderbeiLP.StrictComp in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hx : PrimalFeasible A b x) (hy : DualFeasible A c y) :
    c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  obtain ⟨hx0, hw⟩ := hx
  obtain ⟨hy0, hz⟩ := hy
  have h1 : c ⬝ᵥ x ≤ (Aᵀ *ᵥ y) ⬝ᵥ x := by
    unfold dotProduct
    apply Finset.sum_le_sum
    intro j _
    have hj := hz j
    simp only [dualSlack, Pi.sub_apply] at hj
    exact mul_le_mul_of_nonneg_right (by linarith) (hx0 j)
  have h2 : (Aᵀ *ᵥ y) ⬝ᵥ x = y ⬝ᵥ (A *ᵥ x) := by
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  have h3 : y ⬝ᵥ (A *ᵥ x) ≤ y ⬝ᵥ b := by
    unfold dotProduct
    apply Finset.sum_le_sum
    intro i _
    have hi := hw i
    simp only [primalSlack, Pi.sub_apply] at hi
    exact mul_le_mul_of_nonneg_left (by linarith) (hy0 i)
  rw [dotProduct_comm b y]
  linarith
