-- Prove2me | solution 1 for QuadMatIneq.Petersen.set_identity
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T18:05:52.681101+00:00
-- url     : https://prove2.me/submissions/531cb87f-d2cf-41b8-b7ad-57242435af4b

import Definitions.Def_QuadMatIneq_Petersen_QMI
import Definitions.Def_QuadMatIneq_Petersen_Setup
import Theorems.Thm_QuadMatIneq_Reduced_lemma_A_1
open Matrix QuadMatIneq.Petersen
open scoped MatrixOrder
set_option autoImplicit false
noncomputable section

theorem solution {n p q : ℕ} (Fbar : Matrix (Fin q) (Fin q) ℝ)
    (G : Matrix (Fin q) (Fin n) ℝ) (hFbar : Fbar.PosSemidef) :
    (fun F : Matrix (Fin p) (Fin q) ℝ => F * G) '' uncSet Fbar =
        (fun S : Matrix (Fin p) (Fin q) ℝ => S * CFC.sqrt Fbar * G) ''
          {S | (1 - Sᵀ * S).PosSemidef} ∧
    (fun F : Matrix (Fin p) (Fin q) ℝ => F * G) '' uncSet Fbar =
        {H : Matrix (Fin p) (Fin n) ℝ | (Gᵀ * Fbar * G - Hᵀ * H).PosSemidef} := by
  have hRt : (CFC.sqrt Fbar)ᵀ = CFC.sqrt Fbar := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg Fbar).star_eq
  have hRR : CFC.sqrt Fbar * CFC.sqrt Fbar = Fbar :=
    CFC.sqrt_mul_sqrt_self Fbar (by simpa only [Matrix.nonneg_iff_posSemidef] using hFbar)
  have hf (F : Matrix (Fin p) (Fin q) ℝ) : F ∈ uncSet Fbar ↔
      ∃ S : Matrix (Fin p) (Fin q) ℝ, F = S * CFC.sqrt Fbar ∧
        (1 - Sᵀ * S).PosSemidef := by
    simpa only [uncSet, Set.mem_setOf_eq, hRt, hRR] using
      (QuadMatIneq.Reduced.lemma_A_1 F (CFC.sqrt Fbar)).1
  have hi : (fun F : Matrix (Fin p) (Fin q) ℝ => F * G) '' uncSet Fbar =
      (fun S : Matrix (Fin p) (Fin q) ℝ => S * CFC.sqrt Fbar * G) ''
        {S | (1 - Sᵀ * S).PosSemidef} := by
    ext H
    constructor
    · rintro ⟨F, hF, rfl⟩
      obtain ⟨S, rfl, hS⟩ := (hf F).mp hF
      exact ⟨S, hS, rfl⟩
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S * CFC.sqrt Fbar, (hf _).mpr ⟨S, rfl, hS⟩, rfl⟩
  refine ⟨hi, ?_⟩
  rw [hi]
  ext H
  have hd := (QuadMatIneq.Reduced.lemma_A_1 H (CFC.sqrt Fbar * G)).1
  have hg : (CFC.sqrt Fbar * G)ᵀ * (CFC.sqrt Fbar * G) = Gᵀ * Fbar * G := by
    rw [transpose_mul, hRt, Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt Fbar), hRR,
      ← Matrix.mul_assoc]
  simpa only [Set.mem_image, Set.mem_setOf_eq, hg, Matrix.mul_assoc, eq_comm, and_comm]
    using hd.symm
