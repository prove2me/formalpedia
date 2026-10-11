-- Prove2me | solution 1 for OnsagerReciprocal.timeCorrelation_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-10T23:39:17.756446+00:00
-- url     : https://prove2.me/submissions/0d73c647-ab46-4176-922c-e88c18e85d56

import Mathlib
import Definitions.Def_OnsagerReciprocal_basic
import Theorems.Thm_OnsagerReciprocal_meanFluctuation_dynamics
import Theorems.Thm_OnsagerReciprocal_integrable_norm_pow_mul_fluctuationWeight

open Matrix MeasureTheory
set_option autoImplicit false

private lemma continuous_weight' {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (OnsagerReciprocal.fluctuationWeight β) := by
  unfold OnsagerReciprocal.fluctuationWeight
  fun_prop

private lemma integrable_coord_mul {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ) (hβ : β.PosDef)
    (l k : Fin n) :
    Integrable (fun x : Fin n → ℝ => x l * x k * OnsagerReciprocal.fluctuationWeight β x) := by
  refine (OnsagerReciprocal.integrable_norm_pow_mul_fluctuationWeight β hβ 2).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun x : Fin n → ℝ => x l * x k).mul (continuous_weight' β)
      |>.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    have hw : 0 ≤ OnsagerReciprocal.fluctuationWeight β x := (Real.exp_pos _).le
    have hl := norm_le_pi_norm x l
    have hk := norm_le_pi_norm x k
    rw [Real.norm_eq_abs] at hl hk
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw, pow_two]
    gcongr

private lemma avg_mulVec {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ) (hβ : β.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (i k : Fin n) :
    OnsagerReciprocal.fluctuationAverage β (fun x => (A *ᵥ x) i * x k) =
      ∑ l, A i l * OnsagerReciprocal.fluctuationAverage β (fun x => x l * x k) := by
  unfold OnsagerReciprocal.fluctuationAverage
  have h : ∀ x : Fin n → ℝ, (A *ᵥ x) i * x k * OnsagerReciprocal.fluctuationWeight β x =
      ∑ l, A i l * (x l * x k * OnsagerReciprocal.fluctuationWeight β x) := by
    intro x
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [h]
  rw [integral_finsetSum _ (fun l _ => (integrable_coord_mul β hβ l k).const_mul (A i l)),
    Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, mul_div_assoc]

private lemma meanFluctuation_single_apply {n : ℕ} (lam : Matrix (Fin n) (Fin n) ℝ) (s : ℝ)
    (i l : Fin n) :
    OnsagerReciprocal.meanFluctuation lam s (Pi.single l 1) i =
      NormedSpace.exp ((-s) • lam) i l := by
  unfold OnsagerReciprocal.meanFluctuation
  simp [Matrix.mulVec_single]

private lemma mulVec_single_one_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j l : Fin n) :
    (A *ᵥ Pi.single l 1) j = A j l := by
  simp

private lemma meanConjugate_single {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (l : Fin n) :
    OnsagerReciprocal.meanConjugate β lam t (Pi.single l 1) =
      fun j => (β * NormedSpace.exp ((-t) • lam)) j l := by
  funext j
  unfold OnsagerReciprocal.meanConjugate OnsagerReciprocal.meanFluctuation
  rw [Matrix.mulVec_mulVec, mulVec_single_one_apply]

theorem solution {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (i k : Fin n) (t : ℝ) :
    HasDerivAt (fun s => OnsagerReciprocal.timeCorrelation β lam s i k)
      (-∑ l : Fin n, OnsagerReciprocal.kineticCoeff β lam i l *
        OnsagerReciprocal.fluctuationAverage β
          (fun x => OnsagerReciprocal.meanConjugate β lam t x l * x k)) t := by
  set M : Fin n → Fin n → ℝ := fun l k =>
    OnsagerReciprocal.fluctuationAverage β (fun x => x l * x k) with hM
  have hfun : (fun s => OnsagerReciprocal.timeCorrelation β lam s i k) =
      fun s => ∑ l, OnsagerReciprocal.meanFluctuation lam s (Pi.single l 1) i * M l k := by
    funext s
    unfold OnsagerReciprocal.timeCorrelation
    simp only [meanFluctuation_single_apply]
    exact avg_mulVec β hβ _ i k
  have hconj : ∀ l, OnsagerReciprocal.fluctuationAverage β
      (fun x => OnsagerReciprocal.meanConjugate β lam t x l * x k) =
      ∑ m, (β * NormedSpace.exp ((-t) • lam)) l m * M m k := by
    intro l
    unfold OnsagerReciprocal.meanConjugate OnsagerReciprocal.meanFluctuation
    simp only [Matrix.mulVec_mulVec]
    exact avg_mulVec β hβ _ l k
  have hder : ∀ l, HasDerivAt
      (fun s => OnsagerReciprocal.meanFluctuation lam s (Pi.single l 1) i * M l k)
      ((-(OnsagerReciprocal.kineticCoeff β lam *ᵥ
        OnsagerReciprocal.meanConjugate β lam t (Pi.single l 1))) i * M l k) t := by
    intro l
    have h := (OnsagerReciprocal.meanFluctuation_dynamics β lam hβ (Pi.single l 1)).2 t
    exact (hasDerivAt_pi.1 h i).mul_const (M l k)
  rw [hfun]
  refine (HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => hder l)).congr_deriv ?_
  simp only [hconj, meanConjugate_single, Pi.neg_apply]
  simp only [Matrix.mulVec, dotProduct]
  simp only [neg_mul, Finset.sum_neg_distrib, neg_inj, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring
