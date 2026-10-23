-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.hermitian_moment_implication
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:11:21.386914+00:00
-- url     : https://prove2.me/submissions/10e1ab9c-71e8-4e18-9d27-f06d5af60e64

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

lemma X7_powerTrace_eq_sum {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian) (k : ℕ) :
    QAlgorithms.Papers.Independent.Information100.P19.powerTrace X k =
      ∑ i, hX.eigenvalues i ^ k := by
  unfold QAlgorithms.Papers.Independent.Information100.P19.powerTrace
  have h : (X ^ k).trace = ∑ i, ((hX.eigenvalues i : ℂ)) ^ k := by
    conv_lhs => rw [hX.spectral_theorem]
    rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
    simp [Matrix.diagonal_pow, Matrix.trace_diagonal]
  rw [h]
  simp [← Complex.ofReal_pow, ← Complex.ofReal_sum]

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution (d : ℕ) (hd : 0<d) (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : X.IsHermitian) (ht : 0<powerTrace X 1)
    (h : powerTrace X 2^2 ≤ powerTrace X 1*powerTrace X 3) :
    powerTrace X 2^3 ≤ powerTrace X 1^2*powerTrace X 4 := by
  simp only [X7_powerTrace_eq_sum X hX] at ht h ⊢
  set l := hX.eigenvalues
  have hcs : (∑ i, l i ^ 3) ^ 2 ≤ (∑ i, l i ^ 2) * ∑ i, l i ^ 4 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => l i) (fun i => l i ^ 2)
    have e1 : ∑ i, l i * l i ^ 2 = ∑ i, l i ^ 3 := Finset.sum_congr rfl (fun i _ => by ring)
    have e2 : ∑ i, (l i ^ 2) ^ 2 = ∑ i, l i ^ 4 := Finset.sum_congr rfl (fun i _ => by ring)
    rw [e1, e2] at this; exact this
  have hp2 : 0 < ∑ i, l i ^ 2 := by
    rcases (Finset.sum_nonneg (fun i _ => sq_nonneg (l i))).lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (l i))).mp h'.symm
      have : ∑ i, l i ^ 1 = 0 := Finset.sum_eq_zero (fun i hi => by
        have := hz i hi; simp at this; simp [this])
      linarith
  set p1 := ∑ i, l i ^ 1
  set p2 := ∑ i, l i ^ 2
  set p3 := ∑ i, l i ^ 3
  set p4 := ∑ i, l i ^ 4
  have h4 : p2 ^ 4 ≤ p1 ^ 2 * (p2 * p4) := by
    have e1 : p2 ^ 4 = (p2 ^ 2) ^ 2 := by ring
    have e2 : (p2 ^ 2) ^ 2 ≤ (p1 * p3) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h 2
    have e3 : (p1 * p3) ^ 2 ≤ p1 ^ 2 * (p2 * p4) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    linarith
  have : p2 * p2 ^ 3 ≤ p2 * (p1 ^ 2 * p4) := by nlinarith
  exact le_of_mul_le_mul_left this hp2
