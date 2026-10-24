-- Prove2me | solution 1 for SiweiK24.neumann_transfer
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T18:06:25.825388+00:00
-- url     : https://prove2.me/submissions/d2164e9a-4f6e-48fc-ab99-2d93c32cb11c

import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false


/-- The abstract Banach-space perturbation statement in K24, Section 4.
The equivalence is constructed using the convergent Neumann series. -/
theorem solution
    (X Y : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A : X ≃L[ℝ] Y) (R : X →L[ℝ] Y) (C_A : ℝ)
    (hC : 0 < C_A)
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ C_A)
    (hR : C_A * ‖R‖ < (1 / 2 : ℝ)) :
    ∃ B : X ≃L[ℝ] Y,
      B.toContinuousLinearMap = A.toContinuousLinearMap + R ∧
      ‖B.symm.toContinuousLinearMap‖ ≤ 2 * C_A := by
  let T : X →L[ℝ] X := A.symm.toContinuousLinearMap.comp R
  have hT : ‖T‖ < 1 := by
    calc
      ‖T‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖R‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C_A * ‖R‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg R)
      _ < 1 := by linarith
  let U : (X →L[ℝ] X)ˣ := Units.oneSub (-T) (by simpa using hT)
  let B : X ≃L[ℝ] Y := (ContinuousLinearEquiv.ofUnit U).trans A
  have hB : B.toContinuousLinearMap = A.toContinuousLinearMap + R := by
    ext x
    change A ((1 - -T) x) = A x + R x
    simp [T]
  refine ⟨B, hB, ?_⟩
  have hB_apply (x : X) : B x = A x + R x :=
    congrArg (fun f : X →L[ℝ] Y => f x) hB
  have h_bound (x : X) :
      ‖x‖ ≤ C_A * ‖B x‖ + (C_A * ‖R‖) * ‖x‖ := by
    have hAx : A x = B x - R x := by rw [hB_apply]; simp
    calc
      ‖x‖ = ‖A.symm (A x)‖ := by simp
      _ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖A x‖ :=
        A.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ C_A * ‖A x‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      _ ≤ C_A * (‖B x‖ + ‖R x‖) := by
        rw [hAx]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hC.le
      _ ≤ C_A * (‖B x‖ + ‖R‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (R.le_opNorm x)) hC.le
      _ = C_A * ‖B x‖ + (C_A * ‖R‖) * ‖x‖ := by ring
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith [hC])
  intro y
  have hy := h_bound (B.symm y)
  rw [B.apply_symm_apply] at hy
  have hsmall := mul_le_mul_of_nonneg_right hR.le (norm_nonneg (B.symm y))
  change ‖B.symm y‖ ≤ 2 * C_A * ‖y‖
  nlinarith

#print axioms solution
