-- Prove2me | solution 1 for PhaseCut.Tight.corollary_4_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:16:11.820168+00:00
-- url     : https://prove2.me/submissions/bf0205ed-a752-44ed-9bb0-394f2da0324c

import Mathlib
import Definitions.Def_PhaseCut_Tight_Defs

open Matrix
open scoped ComplexOrder

namespace RRAux_PhaseCut

section Abstract

variable {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (Q : Matrix (Fin p) (Fin n) ℂ)
  (D Di : Matrix (Fin n) (Fin n) ℂ)

lemma psi_phi (hQA : Q * A = 1) (hDiD : Di * D = 1) (hDDi : D * Di = 1)
    (X : Matrix (Fin p) (Fin p) ℂ) :
    Q * D * (Di * A * X * Aᴴ * Di) * D * Qᴴ = X := by
  have hAQ : Aᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQA, conjTranspose_one]
  have e1 : ∀ M : Matrix (Fin n) (Fin p) ℂ, D * (Di * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hDDi, Matrix.one_mul]
  have e2 : ∀ M : Matrix (Fin p) (Fin p) ℂ, Q * (A * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hQA, Matrix.one_mul]
  have e3 : ∀ M : Matrix (Fin n) (Fin p) ℂ, Di * (D * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hDiD, Matrix.one_mul]
  simp only [Matrix.mul_assoc, e1, e2, e3, hAQ, Matrix.mul_one]

lemma mod_zero (hQA : Q * A = 1) (hDDi : D * Di = 1) (X : Matrix (Fin p) (Fin p) ℂ) :
    D * (1 - A * Q) * D * (Di * A * X * Aᴴ * Di) = 0 := by
  have h0 : (1 - A * Q) * A = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hQA, Matrix.mul_one, sub_self]
  have e : D * (1 - A * Q) * D * (Di * A * X * Aᴴ * Di)
      = D * ((1 - A * Q) * A) * X * Aᴴ * Di := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc D Di, hDDi, Matrix.one_mul]
  rw [e, h0]; simp

lemma trB_phi (hQA : Q * A = 1) (hDiD : Di * D = 1) (hDDi : D * Di = 1)
    (X : Matrix (Fin p) (Fin p) ℂ) :
    (D * Qᴴ * Q * D * (Di * A * X * Aᴴ * Di)).trace = X.trace := by
  have hAQ : Aᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQA, conjTranspose_one]
  have e : D * Qᴴ * Q * D * (Di * A * X * Aᴴ * Di) = D * (Qᴴ * X * Aᴴ * Di) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc D Di, hDDi, Matrix.one_mul, ← Matrix.mul_assoc Q A, hQA, Matrix.one_mul]
  rw [e, trace_mul_comm]
  have e2 : Qᴴ * X * Aᴴ * Di * D = Qᴴ * (X * Aᴴ) := by
    rw [Matrix.mul_assoc, hDiD, Matrix.mul_one, Matrix.mul_assoc]
  rw [e2, trace_mul_comm, Matrix.mul_assoc, hAQ, Matrix.mul_one]

lemma trB_U (U : Matrix (Fin n) (Fin n) ℂ) :
    (D * Qᴴ * Q * D * U).trace = (Q * D * U * D * Qᴴ).trace := by
  have e : D * Qᴴ * Q * D * U = (D * Qᴴ) * (Q * D * U) := by simp only [Matrix.mul_assoc]
  rw [e, trace_mul_comm]
  simp only [Matrix.mul_assoc]

lemma key_zero (hQA : Q * A = 1) (hP : (A * Q)ᴴ = A * Q) (hDh : Dᴴ = D)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U.PosSemidef) (htr : (D * (1 - A * Q) * D * U).trace = 0) :
    (1 - A * Q) * (D * U) = 0 := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ, U = star B * B := by
    open scoped MatrixOrder in
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hU.nonneg
  rw [star_eq_conjTranspose] at hB
  set C := (1 - A * Q) * D with hC
  have hidem : (1 - A * Q) * (1 - A * Q) = 1 - A * Q := by
    have : A * Q * (A * Q) = A * Q := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q A, hQA, Matrix.one_mul]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, this, sub_self, sub_zero]
  have hCh : Cᴴ = D * (1 - A * Q) := by
    rw [hC, conjTranspose_mul, hDh, conjTranspose_sub, conjTranspose_one, hP]
  have hM : D * (1 - A * Q) * D = Cᴴ * C := by
    rw [hCh, hC]; simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 - A * Q) (1 - A * Q) D, hidem]
  rw [hM, hB] at htr
  have htr2 : ((C * Bᴴ) * (C * Bᴴ)ᴴ).trace = 0 := by
    rw [← htr, conjTranspose_mul, conjTranspose_conjTranspose]
    calc (C * Bᴴ * (B * Cᴴ)).trace = (C * (Bᴴ * B * Cᴴ)).trace := by simp only [Matrix.mul_assoc]
      _ = (Bᴴ * B * Cᴴ * C).trace := by rw [trace_mul_comm]
      _ = (Cᴴ * C * (Bᴴ * B)).trace := by
          rw [show Bᴴ * B * Cᴴ * C = (Bᴴ * B) * (Cᴴ * C) by simp only [Matrix.mul_assoc],
            trace_mul_comm]
  have h0 : C * Bᴴ = 0 := trace_mul_conjTranspose_self_eq_zero_iff.1 htr2
  rw [← Matrix.mul_assoc, ← hC, hB, ← Matrix.mul_assoc, h0, Matrix.zero_mul]

lemma A_psi_A (hP : (A * Q)ᴴ = A * Q) (hDh : Dᴴ = D)
    (U : Matrix (Fin n) (Fin n) ℂ) (hUh : Uᴴ = U) (hK : (1 - A * Q) * (D * U) = 0) :
    A * (Q * D * U * D * Qᴴ) * Aᴴ = D * U * D := by
  have h0 : A * Q * (D * U) = D * U := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hK; exact hK.symm
  have h1 : A * Q * (D * U * D) = D * U * D := by
    rw [show A * Q * (D * U * D) = A * Q * (D * U) * D by simp only [Matrix.mul_assoc], h0]
  have h2 : D * U * D * (A * Q) = D * U * D := by
    have := congrArg conjTranspose h1
    rw [conjTranspose_mul, hP] at this
    simpa only [conjTranspose_mul, hDh, hUh, Matrix.mul_assoc] using this
  have e : A * (Q * D * U * D * Qᴴ) * Aᴴ = A * Q * (D * U * D) * (Qᴴ * Aᴴ) := by
    simp only [Matrix.mul_assoc]
  rw [e, h1, ← conjTranspose_mul, hP, h2]

lemma phi_psi (hP : (A * Q)ᴴ = A * Q) (hDh : Dᴴ = D) (hDiD : Di * D = 1) (hDDi : D * Di = 1)
    (U : Matrix (Fin n) (Fin n) ℂ) (hUh : Uᴴ = U) (hK : (1 - A * Q) * (D * U) = 0) :
    Di * A * (Q * D * U * D * Qᴴ) * Aᴴ * Di = U := by
  have e : Di * A * (Q * D * U * D * Qᴴ) * Aᴴ * Di = Di * (A * (Q * D * U * D * Qᴴ) * Aᴴ) * Di := by
    simp only [Matrix.mul_assoc]
  rw [e, A_psi_A A Q D hP hDh U hUh hK]
  simp only [Matrix.mul_assoc]
  rw [hDDi, Matrix.mul_one, ← Matrix.mul_assoc, hDiD, Matrix.one_mul]

end Abstract

open PhaseCut.Tight

section Concrete

variable {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)

lemma pinv_mul (hA : Function.Injective A.mulVec) : pinv A * A = 1 := by
  have hinj : Function.Injective (Aᴴ * A).mulVec := by
    intro u v huv
    have h0 : (Aᴴ * A) *ᵥ (u - v) = 0 := by rw [mulVec_sub, huv, sub_self]
    have h1 : star (u - v) ⬝ᵥ ((Aᴴ * A) *ᵥ (u - v)) = 0 := by rw [h0, dotProduct_zero]
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star,
      dotProduct_star_self_eq_zero] at h1
    have : A *ᵥ u = A *ᵥ v := by rw [← sub_eq_zero, ← mulVec_sub]; exact h1
    exact hA this
  have hU : IsUnit (Aᴴ * A) := mulVec_injective_iff_isUnit.1 hinj
  unfold pinv
  rw [Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hU)]

lemma proj_herm : (A * pinv A)ᴴ = A * pinv A := by
  unfold pinv
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv,
    conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma D_herm : (D b)ᴴ = D b := by
  unfold D; rw [diagonal_conjTranspose]; congr 1; funext i; simp

lemma Dinv_herm : (Dinv b)ᴴ = Dinv b := by
  unfold Dinv; rw [diagonal_conjTranspose]; congr 1; funext i; simp

lemma D_Dinv (hb : ∀ i, b i ≠ 0) : D b * Dinv b = 1 := by
  unfold D Dinv; rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
  exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (hb i))

lemma Dinv_D (hb : ∀ i, b i ≠ 0) : Dinv b * D b = 1 := by
  unfold D Dinv; rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 (hb i))

noncomputable def Psi (U : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  pinv A * D b * U * D b * (pinv A)ᴴ

lemma rank_phi_le (X : Matrix (Fin p) (Fin p) ℂ) : (Phi A b X).rank ≤ X.rank := by
  unfold Phi
  exact (rank_mul_le_left _ _).trans ((rank_mul_le_left _ _).trans (rank_mul_le_right _ _))

lemma rank_psi_le (U : Matrix (Fin n) (Fin n) ℂ) : (Psi A b U).rank ≤ U.rank := by
  unfold Psi
  exact (rank_mul_le_left _ _).trans ((rank_mul_le_left _ _).trans (rank_mul_le_right _ _))

lemma phi_feas (hA : Function.Injective A.mulVec) (hb : ∀ i, b i ≠ 0)
    (X : Matrix (Fin p) (Fin p) ℂ) (hX : X ∈ phaseLiftFeasible A b) :
    Phi A b X ∈ phaseCutModFeasible A b := by
  obtain ⟨hXp, hXd⟩ := hX
  refine ⟨?_, ?_, ?_⟩
  · have e : Phi A b X = (Dinv b * A) * X * (Dinv b * A)ᴴ := by
      unfold Phi; rw [conjTranspose_mul, Dinv_herm]; simp only [Matrix.mul_assoc]
    rw [e]; exact hXp.mul_mul_conjTranspose_same _
  · intro i
    have e : Phi A b X = Dinv b * (A * X * Aᴴ) * Dinv b := by
      unfold Phi; simp only [Matrix.mul_assoc]
    rw [e]
    unfold Dinv
    rw [mul_diagonal, diagonal_mul, hXd i]
    have := Complex.ofReal_ne_zero.2 (hb i)
    field_simp
  · unfold Mmat Phi
    rw [mod_zero A (pinv A) (D b) (Dinv b) (pinv_mul A hA) (D_Dinv b hb), trace_zero]

lemma psi_feas (hA : Function.Injective A.mulVec) (hb : ∀ i, b i ≠ 0)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ phaseCutModFeasible A b) :
    Psi A b U ∈ phaseLiftFeasible A b ∧ Phi A b (Psi A b U) = U := by
  obtain ⟨hUp, hUd, hUt⟩ := hU
  have hK := key_zero A (pinv A) (D b) (pinv_mul A hA) (proj_herm A) (D_herm b) U hUp hUt
  have hUh : Uᴴ = U := hUp.isHermitian
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have e : Psi A b U = (pinv A * D b) * U * (pinv A * D b)ᴴ := by
      unfold Psi; rw [conjTranspose_mul, D_herm]; simp only [Matrix.mul_assoc]
    rw [e]; exact hUp.mul_mul_conjTranspose_same _
  · intro i
    unfold Psi
    rw [A_psi_A A (pinv A) (D b) (proj_herm A) (D_herm b) U hUh hK]
    unfold D
    rw [mul_diagonal, diagonal_mul, hUd i]
    ring
  · unfold Phi Psi
    exact phi_psi A (pinv A) (D b) (Dinv b) (proj_herm A) (D_herm b) (Dinv_D b hb) (D_Dinv b hb)
      U hUh hK

lemma psi_phi' (hA : Function.Injective A.mulVec) (hb : ∀ i, b i ≠ 0)
    (X : Matrix (Fin p) (Fin p) ℂ) : Psi A b (Phi A b X) = X := by
  unfold Psi Phi
  exact psi_phi A (pinv A) (D b) (Dinv b) (pinv_mul A hA) (Dinv_D b hb) (D_Dinv b hb) X

lemma trB_phi' (hA : Function.Injective A.mulVec) (hb : ∀ i, b i ≠ 0)
    (X : Matrix (Fin p) (Fin p) ℂ) : (Bmat A b * Phi A b X).trace = X.trace := by
  unfold Bmat Phi
  exact trB_phi A (pinv A) (D b) (Dinv b) (pinv_mul A hA) (Dinv_D b hb) (D_Dinv b hb) X

lemma trB_U' (U : Matrix (Fin n) (Fin n) ℂ) : (Bmat A b * U).trace = (Psi A b U).trace := by
  unfold Bmat Psi
  exact trB_U (pinv A) (D b) U

end Concrete

end RRAux_PhaseCut

open PhaseCut.Tight Matrix in
theorem solution {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hb : ∀ i, b i ≠ 0) (hsol : IsSolvable A b) :
    IsTight (phaseLiftOptimal A b) → IsTight (phaseCutModOptimal A b) := by
  rintro ⟨X0, hS, hr⟩
  have hX0 : X0 ∈ phaseLiftOptimal A b := by rw [hS]; rfl
  have huniq : ∀ Y ∈ phaseLiftOptimal A b, Y = X0 := fun Y hY => by rw [hS] at hY; exact hY
  refine ⟨Phi A b X0, ?_, ?_⟩
  · ext U
    constructor
    · rintro ⟨hUf, hUmin⟩
      obtain ⟨hPf, hPP⟩ := RRAux_PhaseCut.psi_feas A b hA hb U hUf
      have hopt : RRAux_PhaseCut.Psi A b U ∈ phaseLiftOptimal A b := by
        refine ⟨hPf, fun Y hY => ?_⟩
        rw [← RRAux_PhaseCut.trB_U', ← RRAux_PhaseCut.trB_phi' A b hA hb Y]
        exact hUmin _ (RRAux_PhaseCut.phi_feas A b hA hb Y hY)
      rw [Set.mem_singleton_iff, ← hPP, huniq _ hopt]
    · intro hU
      rw [Set.mem_singleton_iff] at hU
      subst hU
      refine ⟨RRAux_PhaseCut.phi_feas A b hA hb X0 hX0.1, fun V hV => ?_⟩
      rw [RRAux_PhaseCut.trB_phi' A b hA hb, RRAux_PhaseCut.trB_U']
      exact hX0.2 _ (RRAux_PhaseCut.psi_feas A b hA hb V hV).1
  · apply le_antisymm
    · rw [← hr]; exact RRAux_PhaseCut.rank_phi_le A b X0
    · rw [← hr]
      calc X0.rank = (RRAux_PhaseCut.Psi A b (Phi A b X0)).rank := by
            rw [RRAux_PhaseCut.psi_phi' A b hA hb]
        _ ≤ (Phi A b X0).rank := RRAux_PhaseCut.rank_psi_le A b _

#print axioms solution
