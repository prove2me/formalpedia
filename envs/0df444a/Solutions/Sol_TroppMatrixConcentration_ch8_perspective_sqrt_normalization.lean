-- Prove2me | solution 1 for TroppMatrixConcentration.ch8_perspective_sqrt_normalization
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:48:25.624013+00:00
-- url     : https://prove2.me/submissions/11b38826-eb09-4d56-ba57-e24c1dd7b95d

import Definitions.Def_TroppMatrixConcentration_ch8_entropy

open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open TroppMatrixConcentration

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (hA : A.PosDef) :
    let S := ch8_matrixFunction Real.sqrt A
    let R := ch8_matrixFunction (fun x => (Real.sqrt x)⁻¹) A
    S.IsHermitian ∧ R.IsHermitian ∧ S * S = A ∧ R * S = 1 ∧ S * R = 1 := by
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) := by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).continuousOn f
  have hpos (x : ℝ) (hx : x ∈ spectrum ℝ A) : 0 < x :=
    hA.isStrictlyPositive.spectrum_pos hx
  dsimp only [ch8_matrixFunction]
  refine ⟨cfc_predicate _ A, cfc_predicate _ A, ?_, ?_, ?_⟩
  · rw [← cfc_mul _ _ A (hcont _) (hcont _)]
    calc
      cfc (fun x => Real.sqrt x * Real.sqrt x) A = cfc (fun x : ℝ => x) A :=
        cfc_congr fun x hx => Real.mul_self_sqrt (hpos x hx).le
      _ = A := cfc_id' ℝ A hA.isHermitian
  · rw [← cfc_mul _ _ A (hcont _) (hcont _)]
    calc
      cfc (fun x => (Real.sqrt x)⁻¹ * Real.sqrt x) A = cfc (fun _ : ℝ => 1) A :=
        cfc_congr fun x hx => inv_mul_cancel₀ (Real.sqrt_pos.mpr (hpos x hx)).ne'
      _ = 1 := cfc_one ℝ A hA.isHermitian
  · rw [← cfc_mul _ _ A (hcont _) (hcont _)]
    calc
      cfc (fun x => Real.sqrt x * (Real.sqrt x)⁻¹) A = cfc (fun _ : ℝ => 1) A :=
        cfc_congr fun x hx => mul_inv_cancel₀ (Real.sqrt_pos.mpr (hpos x hx)).ne'
      _ = 1 := cfc_one ℝ A hA.isHermitian


