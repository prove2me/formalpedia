-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.contDiff_detGram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:00:46.83455+00:00
-- url     : https://prove2.me/submissions/4b02ae8b-778a-4c3b-b25d-fe3d7cf1c130

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
import Theorems.Thm_ReciprocityTheory_AnForm_P_cellMat_eq
import Theorems.Thm_ReciprocityTheory_AnForm_P_zMat_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open MeasureTheory
noncomputable section
open Matrix Polynomial
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) :
    ContDiff ℝ 2 (detGram N hd m hm) := by
  have hZ : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => zMat N z a b) := by
    intro a b
    by_cases h : b < a
    · simp only [zMat_apply, dif_pos h]; exact contDiff_apply ℝ ℂ _
    · simp only [zMat_apply, dif_neg h]; exact contDiff_const
  have hP : ∀ k a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => (zMat N z ^ k) a b) := by
    intro k
    induction k with
    | zero => intro a b; simp only [pow_zero]; exact contDiff_const
    | succ k ih =>
      intro a b
      simp only [pow_succ, Matrix.mul_apply]
      exact ContDiff.sum fun l _ => (ih a l).mul (hZ l b)
  have hA : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => cellMat N z a b) := by
    intro a b
    simp only [cellMat_eq, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact ContDiff.sum fun k _ => contDiff_const.mul (hP k a b)
  have hS : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => star (cellMat N z a b)) := fun a b => by
    have h := Complex.conjCLE.contDiff.comp (hA a b)
    exact h
  have hM : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ =>
      ((cellMat N z)ᴴ * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) a b) := by
    intro a b
    have e : (fun z : Pairs N → ℂ =>
        ((cellMat N z)ᴴ * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) a b) =
        fun z => ∑ l, star (cellMat N z l a) * (hd l : ℂ) * cellMat N z l b := by
      funext z
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    rw [e]
    exact ContDiff.sum fun l _ => ((hS l a).mul contDiff_const).mul (hA l b)
  have hdet : ContDiff ℝ 2 (fun z : Pairs N → ℂ => (Matrix.submatrix ((cellMat N z).conjTranspose *
      Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).det) := by
    simp only [Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM _ _)
  have h2 : ContDiff ℝ 2 (fun z : Pairs N → ℂ => Complex.reCLM (Matrix.submatrix
      ((cellMat N z).conjTranspose * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z)
      (Fin.castLE hm) (Fin.castLE hm)).det) := Complex.reCLM.contDiff.comp hdet
  unfold detGram
  simpa only [Complex.reCLM_apply] using h2
end ReciprocityTheory.AnForm.P
