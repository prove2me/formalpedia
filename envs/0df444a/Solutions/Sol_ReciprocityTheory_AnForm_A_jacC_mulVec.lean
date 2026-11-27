-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.jacC_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:24:05.636111+00:00
-- url     : https://prove2.me/submissions/38efaeff-f9c8-4c84-addf-7bed56dd9280

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
theorem _root_.solution (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z w : Fin D → ℂ) :
    jacC τ z *ᵥ w = fderiv ℂ τ z w := by
  rw [jacC_eq_toMatrix', LinearMap.toMatrix'_mulVec]
  rfl
end ReciprocityTheory.AnForm.A
