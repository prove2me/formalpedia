-- Prove2me | solution 1 for WassKF.Reform.inner_minimization_over_G
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:07:32.929883+00:00
-- url     : https://prove2.me/submissions/750c18d9-2280-4a5b-b85c-e33fcf0db198

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_sdpObjective

set_option autoImplicit false

open Matrix

lemma trace_form {ι κ : Type*} [Fintype ι] [Fintype κ] (Δ : Matrix ι κ ℝ) (P : Matrix κ κ ℝ) :
    (Δ * P * Δᵀ).trace = ∑ i, (Δ i) ⬝ᵥ (P *ᵥ Δ i) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma trace_fromBlocks' {a b : Type*} [Fintype a] [Fintype b] (A : Matrix a a ℝ) (B : Matrix a b ℝ)
    (C : Matrix b a ℝ) (D : Matrix b b ℝ) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem solution {n m : ℕ}
    (S : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) (hS : S.PosDef) :
    IsLeast (Set.range fun G : Matrix (Fin n) (Fin m) ℝ =>
        ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (-G) (-Gᵀ) (Gᵀ * G))ᵀ * S).trace)
      (WassersteinDRO.Shrinkage.sdpObjective S) ∧
    ∀ G : Matrix (Fin n) (Fin m) ℝ,
      ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (-G) (-Gᵀ) (Gᵀ * G))ᵀ * S).trace =
          WassersteinDRO.Shrinkage.sdpObjective S ↔
        G = S.toBlocks₁₂ * S.toBlocks₂₂⁻¹ := by
  set P := S.toBlocks₂₂ with hPdef
  set Q := S.toBlocks₁₂ with hQdef
  set R := S.toBlocks₁₁ with hRdef
  have hP : P.PosDef := hS.submatrix Sum.inr_injective
  have hP' : P.IsHermitian := hP.isHermitian
  have hPT : Pᵀ = P := by
    have := hP'.eq; simpa using this
  have hQT : S.toBlocks₂₁ = Qᵀ := by
    ext i j
    have := hS.isHermitian.apply (Sum.inr i) (Sum.inl j)
    simpa [hQdef, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁] using this.symm
  have hunit : IsUnit P := hP.isUnit
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_isUnit_det _ |>.mp hunit)
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_isUnit_det _ |>.mp hunit)
  have hPiT : (P⁻¹)ᵀ = P⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hPT]
  set Gs := Q * P⁻¹ with hGs
  have hval : ∀ G : Matrix (Fin n) (Fin m) ℝ,
      ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (-G) (-Gᵀ) (Gᵀ * G))ᵀ * S).trace =
        WassersteinDRO.Shrinkage.sdpObjective S + ((G - Gs) * P * (G - Gs)ᵀ).trace := by
    intro G
    have hS' : S = Matrix.fromBlocks R Q Qᵀ P := by
      rw [← hQT]; exact (Matrix.fromBlocks_toBlocks S).symm
    have hGsT : Gsᵀ = P⁻¹ * Qᵀ := by
      rw [hGs, Matrix.transpose_mul, hPiT]
    have e1 : G * P * (P⁻¹ * Qᵀ) = G * Qᵀ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP, Matrix.one_mul]
    have e2 : Gs * P * Gᵀ = Q * Gᵀ := by
      rw [hGs, Matrix.mul_assoc Q P⁻¹ P, hPP', Matrix.mul_one]
    have e3 : Gs * P * (P⁻¹ * Qᵀ) = Q * P⁻¹ * Qᵀ := by
      rw [hGs, Matrix.mul_assoc Q P⁻¹ P, hPP', Matrix.mul_one, Matrix.mul_assoc]
    have hexp : (G - Gs) * P * (G - Gs)ᵀ = G * P * Gᵀ - G * Qᵀ - Q * Gᵀ + Q * P⁻¹ * Qᵀ := by
      rw [Matrix.transpose_sub, hGsT, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul, e1, e2, e3]
      abel
    have hobj : WassersteinDRO.Shrinkage.sdpObjective S = (R - Q * P⁻¹ * Qᵀ).trace := by
      unfold WassersteinDRO.Shrinkage.sdpObjective
      rw [hQT]
    have hM : (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (-G) (-Gᵀ) (Gᵀ * G))ᵀ =
        Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (-G) (-Gᵀ) (Gᵀ * G) := by
      simp [Matrix.fromBlocks_transpose]
    rw [hM, hobj, hexp]
    conv_lhs => rw [hS']
    rw [Matrix.fromBlocks_multiply, trace_fromBlocks']
    simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.one_mul, Matrix.neg_mul, Matrix.trace_neg]
    have c1 : (G * P * Gᵀ).trace = (Gᵀ * G * P).trace := by
      rw [Matrix.trace_mul_cycle]
    have c2 : (Q * Gᵀ).trace = (Gᵀ * Q).trace := Matrix.trace_mul_comm _ _
    rw [c1, c2]
    ring
  have hrow : ∀ G : Matrix (Fin n) (Fin m) ℝ, ∀ i, 0 ≤ (G - Gs) i ⬝ᵥ (P *ᵥ (G - Gs) i) := by
    intro G i
    have := hP.posSemidef.dotProduct_mulVec_nonneg ((G - Gs) i)
    simpa using this
  have hnonneg : ∀ G : Matrix (Fin n) (Fin m) ℝ, 0 ≤ ((G - Gs) * P * (G - Gs)ᵀ).trace := by
    intro G
    rw [trace_form]
    exact Finset.sum_nonneg fun i _ => hrow G i
  have hzero : ∀ G : Matrix (Fin n) (Fin m) ℝ, ((G - Gs) * P * (G - Gs)ᵀ).trace = 0 → G = Gs := by
    intro G h
    rw [trace_form] at h
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hrow G i)).1 h
    ext i j
    by_contra hne
    have hrow0 : (G - Gs) i ≠ 0 := by
      intro h0
      apply hne
      have := congrFun h0 j
      simp only [Matrix.sub_apply, Pi.zero_apply] at this
      linarith
    have := hP.dotProduct_mulVec_pos hrow0
    have h3 := h2 i (Finset.mem_univ i)
    simp at this
    linarith
  refine ⟨⟨⟨Gs, ?_⟩, ?_⟩, ?_⟩
  · simp only
    rw [hval]; simp
  · rintro _ ⟨G, rfl⟩
    simp only
    rw [hval]; linarith [hnonneg G]
  · intro G
    rw [hval]
    constructor
    · intro h
      exact hzero G (by linarith)
    · intro h
      rw [h]; simp
