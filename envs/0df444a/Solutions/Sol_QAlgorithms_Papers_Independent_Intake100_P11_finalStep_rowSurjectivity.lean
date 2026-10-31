-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P11.finalStep_rowSurjectivity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-31T00:28:31.911977+00:00
-- url     : https://prove2.me/submissions/0db6f586-48d2-45a9-a8db-b163bc555791

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P11

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Intake100.P11

theorem solution {P : Type*} (prefixFamily : P → Mat2)
    (hPrefix : ∀ p, IsOneModeSymplectic (prefixFamily p)) :
    (∀ A : Mat2, IsOneModeSymplectic A →
      ∃ p : P, ∃ kappa : ℝ, elementary kappa * prefixFamily p = A) ↔
    (∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) →
      ∃ p : P, prefixFamily p 0 0 = a ∧ prefixFamily p 0 1 = b) := by
  constructor
  · intro h a b hab
    have hs : a ^ 2 + b ^ 2 ≠ 0 := by
      rcases hab with ha | hb
      · have hp := sq_pos_of_ne_zero ha
        nlinarith [sq_nonneg b]
      · have hp := sq_pos_of_ne_zero hb
        nlinarith [sq_nonneg a]
    let A : Mat2 := !![b / (a ^ 2 + b ^ 2), -a / (a ^ 2 + b ^ 2); a, b]
    have hA : IsOneModeSymplectic A := by
      simp only [IsOneModeSymplectic, A, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
      field_simp
      <;> ring
    obtain ⟨p, k, hk⟩ := h A hA
    refine ⟨p, ?_, ?_⟩
    · simpa [elementary, Matrix.mul_apply, Fin.sum_univ_two, A] using
        congrArg (fun M : Mat2 => M 1 0) hk
    · simpa [elementary, Matrix.mul_apply, Fin.sum_univ_two, A] using
        congrArg (fun M : Mat2 => M 1 1) hk
  · intro h A hA
    have hrow : A 1 0 ≠ 0 ∨ A 1 1 ≠ 0 := by
      by_contra hn
      push_neg at hn
      simp [IsOneModeSymplectic, hn.1, hn.2] at hA
    obtain ⟨p, hc, hd⟩ := h (A 1 0) (A 1 1) hrow
    have hB := hPrefix p
    unfold IsOneModeSymplectic at hA hB
    rw [hc, hd] at hB
    refine ⟨p, ?_⟩
    by_cases hcz : A 1 0 = 0
    · have hdz : A 1 1 ≠ 0 := hrow.resolve_left (not_not.mpr hcz)
      have hz : -prefixFamily p 1 0 = A 0 0 := by
        apply mul_right_cancel₀ hdz
        rw [hcz] at hA hB
        nlinarith
      refine ⟨-(A 0 1 + prefixFamily p 1 1) / A 1 1, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [elementary, Matrix.mul_apply, Fin.sum_univ_two, hc, hd, hcz, hz]
      all_goals field_simp
      all_goals nlinarith
    · refine ⟨-(A 0 0 + prefixFamily p 1 0) / A 1 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [elementary, Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
      all_goals field_simp
      all_goals nlinarith

#print axioms solution
