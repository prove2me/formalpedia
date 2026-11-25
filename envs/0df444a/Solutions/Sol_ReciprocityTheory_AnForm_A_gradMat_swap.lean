-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.gradMat_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:16.702662+00:00
-- url     : https://prove2.me/submissions/18145209-0ee6-45ac-91c0-43ceabd8f9e7

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Theorems.Thm_ReciprocityTheory_AnForm_A_gradMat_eq_vecMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Filter Topology
open scoped ComplexOrder
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (v w : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    gradMat w v z = (gradMat v w z)ᴴ := by
  rw [gradMat_eq_vecMulVec, gradMat_eq_vecMulVec, conjTranspose_vecMulVec, star_star]
end ReciprocityTheory.AnForm.A
