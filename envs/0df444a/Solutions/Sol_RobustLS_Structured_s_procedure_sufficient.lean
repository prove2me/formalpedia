-- Prove2me | solution 1 for RobustLS.Structured.s_procedure_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:04:27.904507+00:00
-- url     : https://prove2.me/submissions/a624001c-483d-471a-923b-2bc8cf6ac30c

import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

theorem aux_sps_quad {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) (u : Fin m → ℝ) (v : ℝ)
    (ζ : Fin m → ℝ) :
    (Sum.elim ζ (fun _ => (1 : ℝ)) : Fin m ⊕ Unit → ℝ) ⬝ᵥ
      (quadBlockMat T u v *ᵥ Sum.elim ζ (fun _ => (1 : ℝ))) = quadFn T u v ζ := by
  unfold quadBlockMat quadFn
  rw [fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_def,
    Pi.add_apply, mulVec, of_apply, Finset.univ_unique, Finset.sum_singleton, one_mul, mul_one]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [two_mul]
  simp only [mul_comm]
  ring

theorem aux_sps_lin {m p : ℕ} (A : Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) ℝ)
    (B : Fin p → Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) ℝ) (τ : Fin p → ℝ)
    (w : Fin m ⊕ Unit → ℝ) :
    w ⬝ᵥ ((A - ∑ i, τ i • B i) *ᵥ w) = w ⬝ᵥ (A *ᵥ w) - ∑ i, τ i * (w ⬝ᵥ (B i *ᵥ w)) := by
  rw [sub_mulVec, dotProduct_sub, sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]

end RobustLS.Structured

open RobustLS.Structured

theorem solution {m p : ℕ} (T0 : Matrix (Fin m) (Fin m) ℝ) (u0 : Fin m → ℝ)
    (v0 : ℝ) (T : Fin p → Matrix (Fin m) (Fin m) ℝ) (u : Fin p → Fin m → ℝ) (v : Fin p → ℝ)
    (hT0 : T0ᵀ = T0) (hT : ∀ i, (T i)ᵀ = T i)
    (hτ : ∃ τ : Fin p → ℝ, (∀ i, 0 ≤ τ i) ∧
      (quadBlockMat T0 u0 v0 - ∑ i, τ i • quadBlockMat (T i) (u i) (v i)).PosSemidef) :
    ∀ ζ : Fin m → ℝ, (∀ i, 0 ≤ quadFn (T i) (u i) (v i) ζ) → 0 ≤ quadFn T0 u0 v0 ζ := by
  intro ζ hζ
  obtain ⟨τ, hτ0, hpsd⟩ := hτ
  have h := hpsd.dotProduct_mulVec_nonneg (Sum.elim ζ (fun _ => (1 : ℝ)))
  rw [star_trivial, aux_sps_lin, aux_sps_quad] at h
  simp only [aux_sps_quad] at h
  have hs : 0 ≤ ∑ i, τ i * quadFn (T i) (u i) (v i) ζ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hτ0 i) (hζ i)
  linarith
