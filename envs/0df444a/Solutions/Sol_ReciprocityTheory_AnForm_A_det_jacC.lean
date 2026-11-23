-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.det_jacC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:32:25.600793+00:00
-- url     : https://prove2.me/submissions/a0856292-8c8e-4023-afad-a0d6f330dbbd

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_jacC_eq_toMatrix__103ab3916728

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
theorem _root_.solution (τ : (Fin D → ℂ) → (Fin D → ℂ)) (z : Fin D → ℂ) :
    (jacC τ z).det = LinearMap.det (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) := by
  rw [jacC_eq_toMatrix', LinearMap.det_toMatrix']
end ReciprocityTheory.AnForm.A
