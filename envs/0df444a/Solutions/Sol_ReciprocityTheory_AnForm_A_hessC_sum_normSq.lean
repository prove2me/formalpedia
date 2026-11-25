-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessC_sum_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:18:53.49223+00:00
-- url     : https://prove2.me/submissions/cd271fef-5c0a-4191-aadf-11d312ce0bcb

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_complexHessian_sum_normSq_coord


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
theorem _root_.solution (z : Fin D → ℂ) :
    hessC (fun w => ∑ i, Complex.normSq (w i)) z = 1 := by
  exact TraceConjugationCover.complexHessian_sum_normSq_coord z
end ReciprocityTheory.AnForm.A
