-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P50.bell_orthogonal_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:10:54.857551+00:00
-- url     : https://prove2.me/submissions/4a42e5d9-7464-44a9-9f99-68d844e8243e

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50
noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

theorem s110b_sum2 {I : Type*} [Fintype I] (f : I → I → ℂ) :
    ∑ z : Fin 2 → I, f (z 0) (z 1) = ∑ a, ∑ b, f a b := by
  rw [← (finTwoArrowEquiv I).symm.sum_comp, Fintype.sum_prod_type]
  simp [finTwoArrowEquiv]

theorem s110b_comm {n : ℕ} (V : Mat (Qubits n)) (hV : V ∈ orthogonalMatrices n) :
    pureDensity (printedBell n) * tensorPower 2 V = tensorPower 2 V * pureDensity (printedBell n) := by
  obtain ⟨hU, hre⟩ := hV
  have hstar : ∀ x y, star (V x y) = V x y := by
    intro x y; apply Complex.ext <;> simp [hre x y]
  have h1 : V.conjTranspose * V = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  have h2 : V * V.conjTranspose = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  have e1 : ∀ a b, ∑ u, V u a * V u b = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun h1 a) b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hstar, Matrix.one_apply] at this
    exact this
  have e2 : ∀ a b, ∑ u, V a u * V b u = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun h2 a) b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hstar, Matrix.one_apply] at this
    exact this
  set c : ℂ := ((2 : ℂ) ^ n)⁻¹
  have hphi : ∀ x, printedBell n x = if x 0 = x 1 then c else 0 := fun x => rfl
  ext x y
  simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply, tensorPower, Fin.prod_univ_two, hphi]
  have L : ∑ z : Fin 2 → Qubits n, (if x 0 = x 1 then c else 0) *
      (starRingEnd ℂ) (if z 0 = z 1 then c else 0) * (V (z 0) (y 0) * V (z 1) (y 1)) =
      (if x 0 = x 1 then c else 0) * starRingEnd ℂ c * (if y 0 = y 1 then 1 else 0) := by
    rw [s110b_sum2 (fun a b => (if x 0 = x 1 then c else 0) *
      (starRingEnd ℂ) (if a = b then c else 0) * (V a (y 0) * V b (y 1)))]
    simp only [apply_ite (starRingEnd ℂ), map_zero, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases hx : x 0 = x 1
    · simp only [if_pos hx]
      rw [← Finset.mul_sum, e1]
      split_ifs <;> ring
    · simp only [if_neg hx, Finset.sum_const_zero]
      split_ifs <;> ring
  have R : ∑ z : Fin 2 → Qubits n, V (x 0) (z 0) * V (x 1) (z 1) *
      ((if z 0 = z 1 then c else 0) * (starRingEnd ℂ) (if y 0 = y 1 then c else 0)) =
      (if x 0 = x 1 then 1 else 0) * c * starRingEnd ℂ (if y 0 = y 1 then c else 0) := by
    rw [s110b_sum2 (fun a b => V (x 0) a * V (x 1) b *
      ((if a = b then c else 0) * (starRingEnd ℂ) (if y 0 = y 1 then c else 0)))]
    simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.sum_mul, e2]
    split_ifs <;> ring
  rw [L, R]
  by_cases hx : x 0 = x 1 <;> by_cases hy : y 0 = y 1 <;> simp [hx, hy, mul_comm]

theorem s110b_norm (n : ℕ) : ‖printedBell n‖ ^ 2 = 1 / (2 : ℝ) ^ n := by
  rw [EuclideanSpace.norm_sq_eq]
  have hphi : ∀ x, printedBell n x = if x 0 = x 1 then ((2 : ℂ) ^ n)⁻¹ else 0 := fun x => rfl
  simp only [hphi]
  have : ∀ x : Fin 2 → Qubits n, ‖(if x 0 = x 1 then ((2 : ℂ) ^ n)⁻¹ else 0)‖ ^ 2 =
      (fun a b : Qubits n => if a = b then (((2 : ℝ) ^ n)⁻¹) ^ 2 else 0) (x 0) (x 1) := by
    intro x
    by_cases h : x 0 = x 1 <;> simp [h]
  simp only [this]
  rw [← (finTwoArrowEquiv (Qubits n)).symm.sum_comp, Fintype.sum_prod_type]
  simp [finTwoArrowEquiv, Finset.sum_ite_eq, Finset.card_univ, Fintype.card_bool]
  field_simp

end QAlgorithms.Papers.Independent.Advance50.P50

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P50
open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

theorem solution (n : ℕ) :
    pureDensity (printedBell n) ∈ tensorCommutant 2 (orthogonalMatrices n) ∧
    ‖printedBell n‖ ^ 2 = 1 / (2 : ℝ) ^ n := by
  refine ⟨?_, s110b_norm n⟩
  unfold tensorCommutant
  rintro _ ⟨V, hV, rfl⟩
  exact s110b_comm V hV
