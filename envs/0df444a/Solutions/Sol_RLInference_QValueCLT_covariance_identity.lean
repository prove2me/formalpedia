-- Prove2me | solution 1 for RLInference.QValueCLT.covariance_identity
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-23T03:04:47.497998+00:00
-- url     : https://prove2.me/submissions/1d4ecce4-4b37-479f-8bf3-8680a9a71312

import Definitions.Def_RLInference_QValueCLT_Setting
import Mathlib.Tactic.Ring
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

set_option autoImplicit false
open Matrix Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace UQRLCovariance
open RLInference.QValueCLT
variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

lemma block_covariance_general {I K : Type} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K]
    (C : I → K → K → ℝ) (w : I → ℝ) (V : K → ℝ) :
    let B : Matrix I (I × K) ℝ := fun x q => if x = q.1 then V q.2 else 0
    let D : Matrix (I × K) (I × K) ℝ :=
      fun p q => if p.1 = q.1 then C p.1 p.2 q.2 / w p.1 else 0
    ((B * D : Matrix I (I × K) ℝ) * Bᵀ : Matrix I I ℝ) =
      diagonal (fun x => (w x)⁻¹) *
        diagonal (fun x => ∑ i, ∑ j, V i * C x i j * V j) := by
  classical
  dsimp only
  ext x y
  rw [diagonal_mul]
  change (∑ p : I × K, (∑ q : I × K,
      (if x = q.1 then V q.2 else 0) *
        (if q.1 = p.1 then C q.1 q.2 p.2 / w q.1 else 0)) *
      (if y = p.1 then V p.2 else 0)) =
    (w x)⁻¹ * (if x = y then ∑ i, ∑ j, V i * C x i j * V j else 0)
  by_cases hxy : x = y
  · subst y
    simp only [Fintype.sum_prod_type, if_pos rfl,
      ite_mul, zero_mul, mul_ite, mul_zero]
    simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Finset.sum_const_zero]
    simp_rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · simp [Fintype.sum_prod_type, ite_mul, mul_ite, hxy]

lemma block_covariance (P' : S × A → S → ℝ) (w : S × A → ℝ) (V : S → ℝ) :
    ((blockV (S := S) (A := A) V * DP P' w : Matrix (S × A) ((S × A) × S) ℝ) *
      (blockV (S := S) (A := A) V)ᵀ : Matrix (S × A) (S × A) ℝ) =
      diagonal (fun x => (w x)⁻¹) * DQ P' V := by
  exact block_covariance_general (fun x i j => SigmaP P' x i j) w V

lemma reward_diagonal (sig2 w : S × A → ℝ) :
    diagonal (fun x => sig2 x / w x) =
      diagonal (fun x => (w x)⁻¹) * diagonal sig2 := by
  rw [diagonal_mul_diagonal]
  congr 1
  funext x
  simp only [div_eq_mul_inv]
  ring

lemma inner_covariance (γ : ℝ) (P' : S × A → S → ℝ)
    (V : S → ℝ) (sig2 w : S × A → ℝ) :
    fromCols (1 : Matrix (S × A) (S × A) ℝ) (γ • blockV (S := S) (A := A) V) *
        SigmaRP P' sig2 w *
        (fromCols (1 : Matrix (S × A) (S × A) ℝ) (γ • blockV (S := S) (A := A) V))ᵀ =
      diagonal (fun x => (w x)⁻¹) * (diagonal sig2 + γ ^ 2 • DQ P' V) := by
  simp only [SigmaRP, transpose_fromCols, transpose_one, transpose_smul,
    fromCols_mul_fromBlocks, fromCols_mul_fromRows,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    ← pow_two, block_covariance, reward_diagonal]
  rw [Matrix.mul_add, Matrix.mul_smul]

lemma covariance_algebra (γ : ℝ) (P' : S × A → S → ℝ)
    (aStar : S → A) (V : S → ℝ) (sig2 w : S × A → ℝ) :
    gradPhi γ P' aStar V * SigmaRP P' sig2 w * (gradPhi γ P' aStar V)ᵀ =
      SigmaQ γ P' aStar V sig2 w := by
  let H : Matrix (S × A) (S × A) ℝ := (1 - γ • PtildeStar P' aStar)⁻¹
  let B : Matrix (S × A) ((S × A) ⊕ ((S × A) × S)) ℝ :=
    fromCols (1 : Matrix (S × A) (S × A) ℝ) (γ • blockV (S := S) (A := A) V)
  change (H * B) * SigmaRP P' sig2 w * (H * B)ᵀ =
    H * diagonal (fun x => (w x)⁻¹) * (diagonal sig2 + γ ^ 2 • DQ P' V) * Hᵀ
  calc
    _ = H * (B * SigmaRP P' sig2 w * Bᵀ) * Hᵀ := by
      rw [transpose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [show B * SigmaRP P' sig2 w * Bᵀ =
        diagonal (fun x => (w x)⁻¹) * (diagonal sig2 + γ ^ 2 • DQ P' V) from
          inner_covariance γ P' V sig2 w]
      simp only [Matrix.mul_assoc]

end UQRLCovariance

open RLInference.QValueCLT

theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (γ : ℝ) (P : S × A → PMF S) (R : S × A → Measure ℝ) (aStar : S → A)
    (w : S × A → ℝ) (hw_pos : ∀ x, 0 < w x) :
    gradPhi γ (Pmat P) aStar (Vstar (bellmanFix γ (muR R) (Pmat P))) *
        SigmaRP (Pmat P) (sigma2R R) w *
        (gradPhi γ (Pmat P) aStar (Vstar (bellmanFix γ (muR R) (Pmat P))))ᵀ =
      SigmaQ γ (Pmat P) aStar (Vstar (bellmanFix γ (muR R) (Pmat P))) (sigma2R R) w := by
  exact UQRLCovariance.covariance_algebra γ (Pmat P) aStar
    (Vstar (bellmanFix γ (muR R) (Pmat P))) (sigma2R R) w

#print axioms solution
