-- Prove2me | solution 1 for QuadMatIneq.Petersen.slater
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:41:17.175+00:00
-- url     : https://prove2.me/submissions/b2ac9bdc-f8c2-4177-9388-22f9bb0d4c10

import Mathlib
import Definitions.Def_QuadMatIneq_Petersen_QMI
import Definitions.Def_QuadMatIneq_Petersen_Setup

set_option autoImplicit false
open Matrix QuadMatIneq.Petersen

theorem qmp_spec_form {k : Type*} [Fintype k] [DecidableEq k] (N : Matrix k k ℝ) (hN : N.IsHermitian)
    (v : k → ℝ) :
    ∃ w : k → ℝ, v ⬝ᵥ (N *ᵥ v) = ∑ i, hN.eigenvalues i * (w i * w i) := by
  set U : Matrix k k ℝ := (hN.eigenvectorUnitary : Matrix k k ℝ) with hU
  set l : k → ℝ := hN.eigenvalues with hl
  have hNeq : N = U * diagonal l * Uᵀ := by
    have := hN.spectral_theorem
    rw [this]
    simp [hU, hl, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  refine ⟨Uᵀ *ᵥ v, ?_⟩
  conv_lhs => rw [hNeq]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal]
  ring

theorem solution {n p q : ℕ} (Fbar : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin q) (Fin n) ℝ)
    (hFbar : Fbar.PosDef) (hG : G ≠ 0)
    (hN : (petersenN (p := Fin p) Fbar G).IsHermitian) :
    ∃ i, 0 < hN.eigenvalues i := by
  by_contra hcon
  push_neg at hcon
  -- a vector x with G x ≠ 0
  have hx : ∃ x : Fin n → ℝ, G *ᵥ x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hG
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    simpa using this
  obtain ⟨x, hxG⟩ := hx
  have hpos : 0 < (G *ᵥ x) ⬝ᵥ (Fbar *ᵥ (G *ᵥ x)) := by
    simpa using hFbar.dotProduct_mulVec_pos hxG
  set v : Fin n ⊕ Fin p → ℝ := Sum.elim x 0 with hv
  have hform : v ⬝ᵥ ((petersenN (p := Fin p) Fbar G) *ᵥ v) = (G *ᵥ x) ⬝ᵥ (Fbar *ᵥ (G *ᵥ x)) := by
    unfold petersenN
    rw [hv, Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim]
    simp only [Matrix.zero_mulVec, Matrix.mulVec_zero, add_zero, dotProduct_zero, Matrix.neg_mulVec,
      Matrix.one_mulVec, Pi.zero_apply, zero_dotProduct, zero_add]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  obtain ⟨w, hw⟩ := qmp_spec_form _ hN v
  have hle : ∑ i, hN.eigenvalues i * (w i * w i) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (hcon i) (mul_self_nonneg _)
  linarith
