-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P12.pi_eighth_injection
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T23:54:55.496792+00:00
-- url     : https://prove2.me/submissions/236cdbb5-b599-4f62-a4c8-9d4f76bba866

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

open QAlgorithms.Papers.Independent.Intakenext100.P12 in
theorem solution (psi : Bool → ℂ) (hnorm : finiteInner psi psi = 1) :
    QAlgorithms.hadamard.mulVec hadamardPlus = hadamardPlus ∧
    (QAlgorithms.hadamard * star QAlgorithms.phaseS).mulVec hadamardPlus = magicState ∧
    magicBranch false psi = (fun b => paperS.mulVec psi b / (Real.sqrt 2 : ℂ)) ∧
    magicBranch true psi = (fun b => (star paperS).mulVec psi b / (Real.sqrt 2 : ℂ)) ∧
    QAlgorithms.phaseS.mulVec (magicBranch true psi) =
      (fun b => cisPhase (Real.pi / 4) * paperS.mulVec psi b / (Real.sqrt 2 : ℂ)) ∧
    (∀ outcome : Bool, ∑ b, ‖magicBranch outcome psi b‖ ^ 2 = (1 : ℝ) / 2) := by
  -- real facts
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2sc : 2 * Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8) = Real.sqrt 2 / 2 := by
    rw [← Real.sin_two_mul, show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.sin_pi_div_four]
  have hcos : 2 * Real.cos (Real.pi / 8) ^ 2 - 1 = Real.sqrt 2 / 2 := by
    rw [← Real.cos_two_mul, show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four]
  have hcpos : 0 < Real.cos (Real.pi / 8) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsr : Real.sin (Real.pi / 8) = (Real.sqrt 2 - 1) * Real.cos (Real.pi / 8) := by
    have h : Real.sin (Real.pi / 8) * (2 * Real.cos (Real.pi / 8)) =
        ((Real.sqrt 2 - 1) * Real.cos (Real.pi / 8)) * (2 * Real.cos (Real.pi / 8)) := by
      linear_combination h2sc - (Real.sqrt 2 - 1) * hcos - (1 / 2 : ℝ) * hr2
    exact mul_right_cancel₀ (mul_pos two_pos hcpos).ne' h
  have K1r : Real.sqrt 2 / 2 * (Real.cos (Real.pi / 8) + Real.sin (Real.pi / 8)) =
      Real.cos (Real.pi / 8) := by
    linear_combination (Real.sqrt 2 / 2) * hsr + (Real.cos (Real.pi / 8) / 2) * hr2
  have K2r : Real.sqrt 2 / 2 * (Real.cos (Real.pi / 8) - Real.sin (Real.pi / 8)) =
      Real.sin (Real.pi / 8) := by
    linear_combination (-(Real.sqrt 2 / 2 + 1)) * hsr + (-(Real.cos (Real.pi / 8) / 2)) * hr2
  -- complex facts
  have hq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, hr2]; norm_num
  have hqne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := by positivity
    exact_mod_cast this.ne'
  have hqinv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = ((Real.sqrt 2 : ℝ) : ℂ) / 2 := by
    rw [eq_div_iff two_ne_zero, inv_mul_eq_iff_eq_mul₀ hqne, ← sq, hq]
  have K1 : ((Real.sqrt 2 : ℝ) : ℂ) / 2 * (((Real.cos (Real.pi / 8) : ℝ) : ℂ) +
      ((Real.sin (Real.pi / 8) : ℝ) : ℂ)) = ((Real.cos (Real.pi / 8) : ℝ) : ℂ) := by
    exact_mod_cast K1r
  have K2 : ((Real.sqrt 2 : ℝ) : ℂ) / 2 * (((Real.cos (Real.pi / 8) : ℝ) : ℂ) -
      ((Real.sin (Real.pi / 8) : ℝ) : ℂ)) = ((Real.sin (Real.pi / 8) : ℝ) : ℂ) := by
    exact_mod_cast K2r
  have Isq : Complex.I ^ 2 = -1 := Complex.I_sq
  have Cp : cisPhase (Real.pi / 8) = ((Real.cos (Real.pi / 8) : ℝ) : ℂ) +
      ((Real.sin (Real.pi / 8) : ℝ) : ℂ) * Complex.I := by
    unfold cisPhase
    rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have Cm : cisPhase (-Real.pi / 8) = ((Real.cos (Real.pi / 8) : ℝ) : ℂ) -
      ((Real.sin (Real.pi / 8) : ℝ) : ℂ) * Complex.I := by
    unfold cisPhase
    rw [show (-Real.pi / 8 : ℝ) = -(Real.pi / 8) by ring, mul_comm Complex.I, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    ring
  have C4 : cisPhase (Real.pi / 4) = ((Real.sqrt 2 : ℝ) : ℂ) / 2 +
      ((Real.sqrt 2 : ℝ) : ℂ) / 2 * Complex.I := by
    unfold cisPhase
    rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_four, Real.sin_pi_div_four, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hHval : ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by norm_num
  have Hff : QAlgorithms.hadamard false false = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    show ((Real.sqrt 2)⁻¹ : ℂ) = _
    exact hHval
  have Hft : QAlgorithms.hadamard false true = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    show ((Real.sqrt 2)⁻¹ : ℂ) = _
    exact hHval
  have Htf : QAlgorithms.hadamard true false = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    show ((Real.sqrt 2)⁻¹ : ℂ) = _
    exact hHval
  have Htt : QAlgorithms.hadamard true true = -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    show -((Real.sqrt 2)⁻¹ : ℂ) = _
    rw [hHval]
  have hpT : hadamardPlus true = ((Real.sin (Real.pi / 8) : ℝ) : ℂ) := rfl
  have hpF : hadamardPlus false = ((Real.cos (Real.pi / 8) : ℝ) : ℂ) := rfl
  have hs1 : star (if true then Complex.I else (1 : ℂ)) = -Complex.I := by
    show star Complex.I = -Complex.I
    exact Complex.conj_I
  have hs0 : star (if false then Complex.I else (1 : ℂ)) = 1 := by
    show star (1 : ℂ) = 1
    exact star_one ℂ
  have hst1 : star (((Real.cos (Real.pi / 8) : ℝ) : ℂ) - ((Real.sin (Real.pi / 8) : ℝ) : ℂ) *
      Complex.I) = ((Real.cos (Real.pi / 8) : ℝ) : ℂ) + ((Real.sin (Real.pi / 8) : ℝ) : ℂ) *
      Complex.I := by
    rw [Complex.star_def, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
      Complex.conj_I]
    ring
  have hst2 : star (((Real.cos (Real.pi / 8) : ℝ) : ℂ) + ((Real.sin (Real.pi / 8) : ℝ) : ℂ) *
      Complex.I) = ((Real.cos (Real.pi / 8) : ℝ) : ℂ) - ((Real.sin (Real.pi / 8) : ℝ) : ℂ) *
      Complex.I := by
    rw [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
      Complex.conj_I]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext b
    cases b
    · show ∑ j, QAlgorithms.hadamard false j * hadamardPlus j = hadamardPlus false
      rw [Fintype.sum_bool, Hft, Hff, hpT, hpF, hqinv]
      linear_combination K1
    · show ∑ j, QAlgorithms.hadamard true j * hadamardPlus j = hadamardPlus true
      rw [Fintype.sum_bool, Htt, Htf, hpT, hpF, hqinv]
      linear_combination K2
  · have hD : ∀ j, ((star QAlgorithms.phaseS).mulVec hadamardPlus) j =
        star (if j then Complex.I else (1 : ℂ)) * hadamardPlus j := by
      intro j
      rw [Matrix.star_eq_conjTranspose]
      unfold QAlgorithms.phaseS
      rw [Matrix.diagonal_conjTranspose, Matrix.mulVec_diagonal]
      rfl
    funext b
    rw [← Matrix.mulVec_mulVec]
    cases b
    · show ∑ j, QAlgorithms.hadamard false j * ((star QAlgorithms.phaseS).mulVec hadamardPlus) j =
        cisPhase (-Real.pi / 8) / ((Real.sqrt 2 : ℝ) : ℂ)
      rw [Fintype.sum_bool, hD, hD, Hft, Hff, hpT, hpF, hs1, hs0, Cm]
      ring
    · show ∑ j, QAlgorithms.hadamard true j * ((star QAlgorithms.phaseS).mulVec hadamardPlus) j =
        cisPhase (Real.pi / 8) / ((Real.sqrt 2 : ℝ) : ℂ)
      rw [Fintype.sum_bool, hD, hD, Htt, Htf, hpT, hpF, hs1, hs0, Cp]
      ring
  · funext b
    show psi b * magicState (xor false b) = paperS.mulVec psi b / ((Real.sqrt 2 : ℝ) : ℂ)
    unfold paperS
    rw [Matrix.mulVec_diagonal, Bool.false_xor]
    unfold magicState
    ring
  · funext b
    show psi b * magicState (xor true b) = (star paperS).mulVec psi b / ((Real.sqrt 2 : ℝ) : ℂ)
    rw [Matrix.star_eq_conjTranspose]
    unfold paperS
    rw [Matrix.diagonal_conjTranspose, Matrix.mulVec_diagonal]
    cases b
    · show psi false * (cisPhase (Real.pi / 8) / ((Real.sqrt 2 : ℝ) : ℂ)) =
        star (cisPhase (-Real.pi / 8)) * psi false / ((Real.sqrt 2 : ℝ) : ℂ)
      rw [Cp, Cm, hst1]
      ring
    · show psi true * (cisPhase (-Real.pi / 8) / ((Real.sqrt 2 : ℝ) : ℂ)) =
        star (cisPhase (Real.pi / 8)) * psi true / ((Real.sqrt 2 : ℝ) : ℂ)
      rw [Cp, Cm, hst2]
      ring
  · funext b
    show (QAlgorithms.phaseS.mulVec (magicBranch true psi)) b =
      cisPhase (Real.pi / 4) * paperS.mulVec psi b / ((Real.sqrt 2 : ℝ) : ℂ)
    unfold QAlgorithms.phaseS paperS
    rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]
    cases b
    · show 1 * (psi false * (cisPhase (Real.pi / 8) / ((Real.sqrt 2 : ℝ) : ℂ))) =
        cisPhase (Real.pi / 4) * (cisPhase (-Real.pi / 8) * psi false) / ((Real.sqrt 2 : ℝ) : ℂ)
      rw [Cp, Cm, C4]
      linear_combination (-(psi false / ((Real.sqrt 2 : ℝ) : ℂ))) * K1 +
        (-(psi false / ((Real.sqrt 2 : ℝ) : ℂ)) * Complex.I) * K2 +
        (psi false / ((Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt 2 : ℝ) : ℂ) / 2) *
          ((Real.sin (Real.pi / 8) : ℝ) : ℂ)) * Isq
    · show Complex.I * (psi true * (cisPhase (-Real.pi / 8) / ((Real.sqrt 2 : ℝ) : ℂ))) =
        cisPhase (Real.pi / 4) * (cisPhase (Real.pi / 8) * psi true) / ((Real.sqrt 2 : ℝ) : ℂ)
      rw [Cp, Cm, C4]
      linear_combination (-(psi true / ((Real.sqrt 2 : ℝ) : ℂ))) * K2 +
        (-(psi true / ((Real.sqrt 2 : ℝ) : ℂ)) * Complex.I) * K1 +
        (-(psi true / ((Real.sqrt 2 : ℝ) : ℂ)) * (((Real.sin (Real.pi / 8) : ℝ) : ℂ) +
          ((Real.sqrt 2 : ℝ) : ℂ) / 2 * ((Real.sin (Real.pi / 8) : ℝ) : ℂ))) * Isq
  · have hcis1 : ∀ t : ℝ, ‖cisPhase t‖ = 1 := by
      intro t
      unfold cisPhase
      rw [mul_comm]
      exact Complex.norm_exp_ofReal_mul_I t
    have hnormMS : ∀ x : Bool, ‖magicState x‖ ^ 2 = 1 / 2 := by
      intro x
      unfold magicState
      rw [norm_div, hcis1, Complex.norm_of_nonneg (Real.sqrt_nonneg 2), div_pow, hr2]
      norm_num
    have hsum : ∑ i, ‖psi i‖ ^ 2 = 1 := by
      unfold finiteInner at hnorm
      simp only [Complex.conj_mul'] at hnorm
      have : (((∑ i, ‖psi i‖ ^ 2 : ℝ)) : ℂ) = 1 := by
        push_cast
        exact hnorm
      exact_mod_cast this
    intro outcome
    simp only [magicBranch, norm_mul, mul_pow, hnormMS]
    rw [← Finset.sum_mul, hsum]
    norm_num

end
