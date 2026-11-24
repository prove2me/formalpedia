-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.det_fderiv_real_eq_normSq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:30.604105+00:00
-- url     : https://prove2.me/submissions/58d4e2ee-4051-443a-911b-89a3e480e43e

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_jacC
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_restrictScalars_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Matrix
noncomputable section
variable {D E : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (τ : (Fin D → ℂ) → (Fin D → ℂ)) (z : Fin D → ℂ)
    (hτ : DifferentiableAt ℂ τ z) :
    (fderiv ℝ τ z).det = Complex.normSq (jacC τ z).det := by
  rw [(hτ.hasFDerivAt.restrictScalars ℝ).fderiv, det_jacC]
  exact det_restrictScalars_real (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
end ReciprocityTheory.AnForm.A
