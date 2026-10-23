-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.finite_ancilla_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:53:34.51132+00:00
-- url     : https://prove2.me/submissions/1aa2fadc-836f-490d-b6f0-e1b71d75c7cc

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

open Matrix

theorem x8_pad {m : ℕ} (E : Fin m → Matrix B A ℂ) (f : Matrix B A ℂ → ℂ) (hf : f 0 = 0) :
    ∑ j : Fin (m + 1), f (if h : j.val < m then E ⟨j.val, h⟩ else 0) = ∑ i, f (E i) := by
  rw [Fin.sum_univ_castSucc]
  simp [hf]

theorem x8_main [Nonempty A] [Nonempty B]
    (Phi : Superop A B) (hPhi : IsChannel Phi) :
    ∃ r : ℕ, ∃ hr : 0 < r, ∃ U : Matrix (B × Fin r) (A × Fin r) ℂ,
      PartialIsometry U ∧ ∀ rho, Phi rho =
        traceRight (U * (rho ⊗ₖ pureDensity (ket (⟨0,hr⟩ : Fin r))) * Uᴴ) := by
  obtain ⟨m, E, hE, hPhi⟩ := hPhi
  set E' : Fin (m + 1) → Matrix B A ℂ := fun j => if h : j.val < m then E ⟨j.val, h⟩ else 0
    with hE'
  refine ⟨m + 1, Nat.succ_pos m,
    Matrix.of fun (bj : B × Fin (m + 1)) (ai : A × Fin (m + 1)) =>
      if ai.2 = 0 then E' bj.2 bj.1 ai.1 else 0, ?_, ?_⟩
  · set U : Matrix (B × Fin (m + 1)) (A × Fin (m + 1)) ℂ := Matrix.of fun bj ai =>
      if ai.2 = 0 then E' bj.2 bj.1 ai.1 else 0 with hU
    have hUU : Uᴴ * U = Matrix.of fun (ai ai' : A × Fin (m + 1)) =>
        if ai.2 = 0 ∧ ai'.2 = 0 then (if ai.1 = ai'.1 then 1 else 0) else 0 := by
      ext ⟨a, i⟩ ⟨a', i'⟩
      have hk := congrFun (congrFun hE a) a'
      simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, one_apply] at hk
      rw [mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
      simp only [hU, conjTranspose_apply, of_apply]
      by_cases hi : i = 0 <;> by_cases hi' : i' = 0 <;> simp only [hi, hi', if_true, if_false,
        star_zero, zero_mul, mul_zero, Finset.sum_const_zero, and_true, and_false, true_and,
        false_and]
      have := x8_pad E (fun M => ∑ b, star (M b a) * M b a') (by simp)
      simp only [hE'] at this ⊢
      rw [this, ← hk]
    show U * Uᴴ * U = U
    rw [Matrix.mul_assoc, hUU]
    ext ⟨b, j⟩ ⟨a', i'⟩
    rw [mul_apply, Fintype.sum_prod_type]
    simp only [hU, of_apply]
    by_cases hi' : i' = 0
    · simp [hi']
    · simp [hi']
  · intro rho
    rw [hPhi rho]
    have hpad := fun b b' => x8_pad E (fun M => (M * rho * Mᴴ) b b') (by simp)
    ext b b'
    rw [krausApply, Matrix.sum_apply, ← hpad]
    simp only [traceRight, of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_apply, conjTranspose_apply, kroneckerMap_apply, pureDensity, ket, of_apply,
      Fintype.sum_prod_type, EuclideanSpace.single_apply]
    have h0 : (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) = 0 := rfl
    have hc : ∀ p : Prop, [Decidable p] →
        (starRingEnd ℂ) (if p then 1 else 0) = if p then 1 else 0 := by
      intro p _; split_ifs <;> simp
    simp only [h0, hE', hc]
    simp only [ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one, apply_ite star, star_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]

end QAlgorithms.Papers.Independent.Gap48.P36

open scoped Matrix Kronecker in
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P36 QAlgorithms.Papers.Independent.Claimed50.P48 in
theorem solution {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (Phi : Superop A B) (hPhi : IsChannel Phi) :
    ∃ r : ℕ, ∃ hr : 0 < r, ∃ U : Matrix (B × Fin r) (A × Fin r) ℂ,
      PartialIsometry U ∧ ∀ rho, Phi rho =
        traceRight (U * (rho ⊗ₖ pureDensity (ket (⟨0,hr⟩ : Fin r))) * Uᴴ) :=
  x8_main Phi hPhi
