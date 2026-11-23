-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.continuous_mdisc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:51.719978+00:00
-- url     : https://prove2.me/submissions/bca66142-2604-4b73-bc30-ee85e3e218db

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} :
    Continuous (fun A : Fin D → Matrix (Fin D) (Fin D) ℂ => mdisc A) := by
  unfold mdisc
  refine continuous_const.mul (continuous_finset_sum _ fun S _ => continuous_const.mul ?_)
  exact (continuous_finset_sum _ fun k _ => continuous_apply k).matrix_det
end ReciprocityTheory.AnForm.A
