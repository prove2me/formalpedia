-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.det_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:24:34.059737+00:00
-- url     : https://prove2.me/submissions/a289c0fc-d2b5-4982-b29d-9325dd975420

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_FubiniStudyPotentialProductIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProdProofA
import Theorems.Thm_ReciprocityTheory_AnForm_M_block_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
noncomputable section
variable {e e' : ℕ}
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (M1 : Matrix (Fin e) (Fin e) ℂ) (M2 : Matrix (Fin e') (Fin e') ℂ) :
    ((J1 e e')ᵀ * M1 * J1 e e' + (J2 e e')ᵀ * M2 * J2 e e').det = M1.det * M2.det := by
  rw [block_eq, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
end ReciprocityTheory.AnForm.M
