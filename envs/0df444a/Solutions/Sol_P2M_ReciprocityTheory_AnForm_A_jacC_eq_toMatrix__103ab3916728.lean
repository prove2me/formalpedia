-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_jacC_eq_toMatrix__103ab3916728
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:30.537703+00:00
-- url     : https://prove2.me/submissions/3488734b-5bdb-4cff-b9ca-c0f4260b6c5d

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul

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
theorem _root_.solution (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ) :
    jacC τ z = LinearMap.toMatrix' (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin E → ℂ)) := by
  ext a k
  rw [LinearMap.toMatrix'_apply]
  rfl
end ReciprocityTheory.AnForm.A
