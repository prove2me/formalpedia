-- Prove2me | solution 1 for StrongWeakEq.Limit.display_5_12_generator_form
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:17:16.983737+00:00
-- url     : https://prove2.me/submissions/bdcbf5f4-be60-46b5-bb75-fd7806217845

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Discrete_DiscreteModel
import Definitions.Def_StrongWeakEq_Limit_Discretization

set_option autoImplicit false
open StrongWeakEq.Limit

theorem solution {N : ℕ} (f : ℝ → Fin N → (Fin N → ℝ) → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (H : Fin N → ℝ) (u un : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) :
    (kappaN f δ 0 i (u i) + H ⬝ᵥ u i ≤ kappaN f δ 0 i (un i) + H ⬝ᵥ un i) ↔
      (f 0 i (genOf δ u i) + H ⬝ᵥ genOf δ u i ≤ f 0 i (genOf δ un i) + H ⬝ᵥ genOf δ un i) := by
  have hg : ∀ w : Matrix (Fin N) (Fin N) ℝ, genOf δ w i = δ⁻¹ • (w i - Pi.single i (1 : ℝ)) := by
    intro w
    funext j
    simp [genOf, Matrix.one_apply, Pi.single_apply, eq_comm]
  have hk : ∀ w : Matrix (Fin N) (Fin N) ℝ, kappaN f δ 0 i (w i) = f 0 i (genOf δ w i) * δ := by
    intro w
    simp [kappaN, hg]
  have hd : ∀ w : Matrix (Fin N) (Fin N) ℝ, H ⬝ᵥ genOf δ w i = δ⁻¹ * (H ⬝ᵥ w i - H i) := by
    intro w
    rw [hg, dotProduct_smul, dotProduct_sub, smul_eq_mul]
    simp
  rw [hk, hk, hd, hd]
  have hδ0 : δ ≠ 0 := hδ.ne'
  constructor
  · intro h
    have h' : δ * (f 0 i (genOf δ u i) + δ⁻¹ * (H ⬝ᵥ u i - H i)) ≤ δ * (f 0 i (genOf δ un i) + δ⁻¹ * (H ⬝ᵥ un i - H i)) := by
      have e1 : δ * (f 0 i (genOf δ u i) + δ⁻¹ * (H ⬝ᵥ u i - H i)) = f 0 i (genOf δ u i) * δ + H ⬝ᵥ u i - H i := by
        field_simp
        ring
      have e2 : δ * (f 0 i (genOf δ un i) + δ⁻¹ * (H ⬝ᵥ un i - H i)) = f 0 i (genOf δ un i) * δ + H ⬝ᵥ un i - H i := by
        field_simp
        ring
      rw [e1, e2]; linarith
    exact le_of_mul_le_mul_left h' hδ
  · intro h
    have h' := mul_le_mul_of_nonneg_left h hδ.le
    have e1 : δ * (f 0 i (genOf δ u i) + δ⁻¹ * (H ⬝ᵥ u i - H i)) = f 0 i (genOf δ u i) * δ + H ⬝ᵥ u i - H i := by
      field_simp
      ring
    have e2 : δ * (f 0 i (genOf δ un i) + δ⁻¹ * (H ⬝ᵥ un i - H i)) = f 0 i (genOf δ un i) * δ + H ⬝ᵥ un i - H i := by
      field_simp
      ring
    rw [e1, e2] at h'
    linarith
