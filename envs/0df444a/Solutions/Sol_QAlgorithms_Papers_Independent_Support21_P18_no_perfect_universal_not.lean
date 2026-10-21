-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P18.no_perfect_universal_not
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:07:13.35422+00:00
-- url     : https://prove2.me/submissions/f9d0d61d-6d06-4742-9aef-fb84180d5993

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

lemma g66j_state2 (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    IsState (WithLp.toLp 2 ![a, b] : EuclideanSpace ℂ (Fin 2)) := by
  unfold IsState
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, h]

lemma g66j_no_not {m : ℕ} (E : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (hT : ∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
      krausApply E (pureDensity psi) = 1 - pureDensity psi) : False := by
  set c : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hc
  have hc2 : c * c = 1 / 2 := by
    rw [hc, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  have hcn : ‖c‖ ^ 2 = 1 / 2 := by
    rw [hc, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hcc : conj c = c := by rw [hc, Complex.conj_ofReal]
  -- e0
  have h0 := congrFun (congrFun (hT _ (g66j_state2 1 0 (by simp))) 0) 0
  have h1 := congrFun (congrFun (hT _ (g66j_state2 0 1 (by simp))) 1) 1
  simp [krausApply, pureDensity, Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_two] at h0 h1
  have hz0 : ∀ j, E j 0 0 = 0 := by
    have : ∑ j, Complex.normSq (E j 0 0) = 0 := by
      have := congrArg Complex.re h0
      simpa [Complex.mul_conj] using this
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (E j 0 0))).1 this j (by simp)
    exact Complex.normSq_eq_zero.1 this
  have hz1 : ∀ j, E j 1 1 = 0 := by
    have : ∑ j, Complex.normSq (E j 1 1) = 0 := by
      have := congrArg Complex.re h1
      simpa [Complex.mul_conj] using this
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (E j 1 1))).1 this j (by simp)
    exact Complex.normSq_eq_zero.1 this
  have hp := congrFun (congrFun (hT _ (g66j_state2 c c (by rw [hcn]; norm_num))) 0) 1
  have hi := congrFun (congrFun (hT _ (g66j_state2 c (Complex.I * c)
    (by rw [norm_mul, Complex.norm_I, one_mul, hcn]; norm_num))) 0) 1
  simp [krausApply, pureDensity, Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_two, hz0, hz1, hcc] at hp hi
  set S := ∑ j, E j 0 1 * conj (E j 1 0) with hS
  have e1 : (∑ j, E j 0 1 * (c * c) * conj (E j 1 0)) = S * (c * c) := by
    rw [hS, Finset.sum_mul]; exact Finset.sum_congr rfl (fun j _ => by ring)
  have e2 : (∑ j, E j 0 1 * (Complex.I * c * c) * conj (E j 1 0)) = S * (Complex.I * c * c) := by
    rw [hS, Finset.sum_mul]; exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [e1, hc2] at hp
  rw [e2] at hi
  have hi' : S * Complex.I * (1/2) = Complex.I * (1/2) := by
    rw [← hc2]; linear_combination hi
  have hS1 : S = -1 := by linear_combination 2 * hp
  rw [hS1] at hi'
  have := congrArg Complex.im hi'
  norm_num at this

theorem solution :
    ¬ ∃ T : Superop (Fin 2) (Fin 2), IsChannel T ∧
      ∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
        T (pureDensity psi) = orthogonalDensity psi := by
  rintro ⟨T, ⟨m, E, -, hE⟩, h⟩
  exact g66j_no_not E (fun psi hpsi => by rw [← hE]; exact h psi hpsi)

end
