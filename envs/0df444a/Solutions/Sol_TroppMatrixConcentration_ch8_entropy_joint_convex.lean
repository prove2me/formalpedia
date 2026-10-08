-- Prove2me | solution 1 for TroppMatrixConcentration.ch8_entropy_joint_convex
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:50:18.913426+00:00
-- url     : https://prove2.me/submissions/bc6606cd-5e5d-4bf5-b9fe-4aae8150c2c4

import Theorems.Thm_TroppMatrixConcentration_ch8_joint_tensor_representation
import Theorems.Thm_TroppMatrixConcentration_ch8_perspective_convex
import Theorems.Thm_TroppMatrixConcentration_ch8_log_operator_concave
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker
open TroppMatrixConcentration Matrix
set_option autoImplicit false

private lemma left_pos {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (h : A.PosDef) :
    (ch8_joint_left A).PosDef :=
  (h.kronecker Matrix.PosDef.one).submatrix finProdFinEquiv.symm.injective
private lemma right_pos {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (h : A.PosDef) :
    (ch8_joint_right A).PosDef :=
  (Matrix.PosDef.one.kronecker h.transpose).submatrix finProdFinEquiv.symm.injective

private lemma left_combo {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) (a b : ℝ) :
    ch8_joint_left (a • A + b • B) = a • ch8_joint_left A + b • ch8_joint_left B := by
  ext i j
  simp [ch8_joint_left, Matrix.kroneckerMap, add_mul]
  ring
private lemma right_combo {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) (a b : ℝ) :
    ch8_joint_right (a • A + b • B) = a • ch8_joint_right A + b • ch8_joint_right B := by
  ext i j
  simp [ch8_joint_right, Matrix.kroneckerMap, mul_add]
  ring
private lemma eval_combo {d : ℕ} (A B : Matrix (Fin (d*d)) (Fin (d*d)) ℂ) (a b : ℝ) :
    ch8_joint_eval (a • A + b • B) = a * ch8_joint_eval A + b * ch8_joint_eval B := by
  simp [ch8_joint_eval, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
    dotProduct_smul]
private lemma eval_mono {d : ℕ} (A B : Matrix (Fin (d*d)) (Fin (d*d)) ℂ)
    (h : loewnerLE A B) : ch8_joint_eval A ≤ ch8_joint_eval B := by
  have hp := h.dotProduct_mulVec_nonneg ch8_joint_vec
  have hr := (Complex.nonneg_iff.mp hp).1
  simpa [ch8_joint_eval, Matrix.sub_mulVec, dotProduct_sub] using hr

private lemma pd_combo {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : (a • A + b • B).PosDef := by
  exact (CFC.concaveOn_log.1 hA.isStrictlyPositive hB.isStrictlyPositive ha hb hab).posDef

theorem solution {d : ℕ} [NeZero d] :
    ConvexOn ℝ {P : Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ |
      P.1.PosDef ∧ P.2.PosDef} (fun P => ch8_relativeEntropy P.1 P.2) := by
  constructor
  · intro P hP Q hQ a b ha hb hab
    exact ⟨pd_combo _ _ hP.1 hQ.1 a b ha hb hab, pd_combo _ _ hP.2 hQ.2 a b ha hb hab⟩
  · intro P hP Q hQ a b ha hb hab
    have hb' : b = 1 - a := by linarith
    have ha1 : a ≤ 1 := by linarith
    have hpers := ch8_perspective_convex (fun x => -Real.log x)
      ch8_log_operator_concave (ch8_joint_left P.1) (ch8_joint_left Q.1)
      (ch8_joint_right P.2) (ch8_joint_right Q.2)
      (left_pos _ hP.1) (left_pos _ hQ.1) (right_pos _ hP.2) (right_pos _ hQ.2)
      a ha ha1
    rw [← hb', ← left_combo, ← right_combo] at hpers
    have he := eval_mono _ _ hpers
    rw [eval_combo] at he
    change ch8_relativeEntropy (a • P.1 + b • Q.1) (a • P.2 + b • Q.2) ≤
      a * ch8_relativeEntropy P.1 P.2 + b * ch8_relativeEntropy Q.1 Q.2
    rw [ch8_joint_tensor_representation _ _ (pd_combo _ _ hP.1 hQ.1 a b ha hb hab)
      (pd_combo _ _ hP.2 hQ.2 a b ha hb hab),
      ch8_joint_tensor_representation _ _ hP.1 hP.2,
      ch8_joint_tensor_representation _ _ hQ.1 hQ.2]
    have ht : (Matrix.trace (a • P.1 + b • Q.1 - (a • P.2 + b • Q.2))).re =
        a * (Matrix.trace (P.1 - P.2)).re + b * (Matrix.trace (Q.1 - Q.2)).re := by
      simp [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Complex.mul_re]
      ring
    rw [ht]
    nlinarith
