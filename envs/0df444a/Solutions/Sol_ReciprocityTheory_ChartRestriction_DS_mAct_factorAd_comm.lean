-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.mAct_factorAd_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:55.107802+00:00
-- url     : https://prove2.me/submissions/f7713259-9a6a-4379-93e5-51adb1c8c6e4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_big_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mAct_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
variable {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (k : ℕ) (i : Fin k) (a b c d : Fin n) :
    mAct E k a b * factorAd k i c d = factorAd k i c d * mAct E k a b := by
  apply LinearMap.ext
  intro F
  apply big_ext
  intro κ
  simp only [Module.End.mul_apply, mAct_apply, factorAd_apply]
  split_ifs <;> simp [map_sub]
end ReciprocityTheory.ChartRestriction.DS
