-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.wd_normSq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:07.106793+00:00
-- url     : https://prove2.me/submissions/1a565a26-f299-41ed-9189-676c72194229

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution {j : Fin n} {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    wd n j (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) x = wd n j g x * conj (g x) := by
  have hdiff : DifferentiableAt ℂ g x :=
    hg.differentiableAt (by first | norm_num | exact one_le_two | decide | simp)
  have hD : HasFDerivAt g (fderiv ℝ g x) x := (hdiff.restrictScalars ℝ).hasFDerivAt
  have hlin : ∀ v : V n, fderiv ℝ g x (Complex.I • v) = Complex.I * fderiv ℝ g x v := by
    intro v
    rw [hdiff.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  have hc : HasFDerivAt (fun y => conj (g y))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g x)) x :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x hD
  have hh : HasFDerivAt (fun y => g y * conj (g y))
      (g x • (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g x) + conj (g x) • fderiv ℝ g x) x :=
    hD.mul hc
  have hfun : (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) := by
    funext y
    exact (Complex.mul_conj (g y)).symm
  unfold wd
  rw [hfun, hh.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    smul_eq_mul, hlin, map_mul, Complex.conj_I]
  linear_combination (g x * conj (fderiv ℝ g x (bas n j)) / 2) * Complex.I_mul_I
end ReciprocityTheory.L2DbarEstimates.H
