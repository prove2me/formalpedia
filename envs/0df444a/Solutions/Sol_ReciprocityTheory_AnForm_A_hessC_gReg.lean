-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessC_gReg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:32.591554+00:00
-- url     : https://prove2.me/submissions/e42e2d7b-3012-4382-af7e-9ae9f3a22a07

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv2_comp_clm
import Theorems.Thm_ReciprocityTheory_AnForm_A_second_fderiv_regularized_log
import Theorems.Thm_ReciprocityTheory_AnForm_A_gReg_contDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {n : ℕ} {ε : ℝ} (hε : 0 < ε) (i : Fin (n + 1)) (z : Fin (n + 1) → ℂ) :
    hessC (fun y : Fin (n + 1) → ℂ => gReg ε (y i)) z =
      ((cReg ε (z i) : ℝ) : ℂ) • Matrix.single i i 1 := by
  let P : (Fin (n + 1) → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℂ) i
  have hf : (fun y : Fin (n + 1) → ℂ => gReg ε (y i)) = gReg ε ∘ P := rfl
  have hP : ∀ y, P y = y i := fun y => rfl
  ext a b
  simp only [hessC, hf, fderiv2_comp_clm _ P (gReg_contDiff hε), hP]
  by_cases ha : a = i
  · by_cases hb : b = i
    · rw [ha, hb]
      have hs : ‖z i‖ ^ 2 + ε ≠ 0 := by positivity
      have hn : ‖z i‖ ^ 2 = (z i).re ^ 2 + (z i).im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have h1 : fderiv ℝ (fderiv ℝ (gReg ε)) (z i) 1 1 +
          fderiv ℝ (fderiv ℝ (gReg ε)) (z i) Complex.I Complex.I = 4 * cReg ε (z i) := by
        rw [second_fderiv_regularized_log hε, second_fderiv_regularized_log hε]
        simp only [Complex.inner, cReg, hn]
        simp
        field_simp
        ring
      have h2 : fderiv ℝ (fderiv ℝ (gReg ε)) (z i) 1 Complex.I -
          fderiv ℝ (fderiv ℝ (gReg ε)) (z i) Complex.I 1 = 0 := by
        rw [second_fderiv_regularized_log hε, second_fderiv_regularized_log hε]
        simp only [Complex.inner]
        simp
        ring
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      rw [h1, h2]
      simp
    · simp [Pi.single_apply, Ne.symm hb]
  · simp [Pi.single_apply, Ne.symm ha]
end ReciprocityTheory.AnForm.A
