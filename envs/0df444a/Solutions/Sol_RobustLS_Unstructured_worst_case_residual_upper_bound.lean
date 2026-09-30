-- Prove2me | solution 1 for RobustLS.Unstructured.worst_case_residual_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:13:51.527346+00:00
-- url     : https://prove2.me/submissions/d4ce58d4-3fff-4f9a-b2df-9a724fdb66e5

import Definitions.Def_RobustLS_Unstructured_Core
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic
open RobustLS.Unstructured Matrix
open scoped RealInnerProductSpace

private theorem euc_eq_norm {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    eucNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ := by
  have hh : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖^2 = ∑ i,v i^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp
  rw [eucNorm,← hh,Real.sqrt_sq (norm_nonneg _)]

private theorem euc_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    (eucNorm v)^2=∑ i,v i^2 := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
private theorem euc_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ eucNorm v := Real.sqrt_nonneg _
private theorem euc_add {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    eucNorm (v+w) ≤ eucNorm v+eucNorm w := by
  simp only [euc_eq_norm]
  exact norm_add_le _ _
private theorem euc_smul {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ) :
    eucNorm (a • v)=|a| *eucNorm v := by
  simp only [euc_eq_norm]
  change ‖a • (WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ = _
  rw [norm_smul,Real.norm_eq_abs]
private theorem frob_sq {ι κ : Type*} [Fintype ι] [Fintype κ] (X : Matrix ι κ ℝ) :
    frobNorm X^2=∑ i,∑ j,X i j^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
private theorem frob_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (X : Matrix ι κ ℝ) :
    0 ≤ frobNorm X := Real.sqrt_nonneg _

private theorem euc_mul_le_frob {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ι κ ℝ) (v : κ → ℝ) : eucNorm (X *ᵥ v) ≤ frobNorm X*eucNorm v := by
  apply (sq_le_sq₀ (euc_nonneg _) (mul_nonneg (frob_nonneg _) (euc_nonneg _))).mp
  rw [mul_pow,euc_sq,frob_sq,euc_sq,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

private theorem stack_norm {m : ℕ} (x : Fin m → ℝ) :
    eucNorm (Sum.elim x (fun _ : Unit => (-1:ℝ))) = Real.sqrt (eucNorm x^2+1) := by
  rw [eucNorm,euc_sq]
  simp [Fintype.sum_sum_type]

private theorem perturb_eq {n m : ℕ} (A ΔA : Matrix (Fin n) (Fin m) ℝ)
    (b Δb : Fin n → ℝ) (x : Fin m → ℝ) :
    (A+ΔA)*ᵥx-(b+Δb)=(A*ᵥx-b)+(augment ΔA Δb)*ᵥ(Sum.elim x (fun _ : Unit => (-1:ℝ))) := by
  ext i
  simp [Matrix.mulVec, dotProduct, augment, Fintype.sum_sum_type,add_mul,Finset.sum_add_distrib]
  ring

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) (x : Fin m → ℝ) (ΔA : Matrix (Fin n) (Fin m) ℝ) (Δb : Fin n → ℝ)
    (hΔ : frobNorm (augment ΔA Δb) ≤ 1) :
    perturbedResidual A b ΔA Δb x ≤ eucNorm (A *ᵥ x - b) + Real.sqrt (eucNorm x ^ 2 + 1) := by
  rw [perturbedResidual,perturb_eq]
  apply le_trans (euc_add _ _)
  have hh := euc_mul_le_frob (augment ΔA Δb) (Sum.elim x (fun _ : Unit => (-1:ℝ)))
  rw [stack_norm] at hh
  have hh' := mul_le_mul_of_nonneg_right hΔ (Real.sqrt_nonneg (eucNorm x^2+1))
  linarith
