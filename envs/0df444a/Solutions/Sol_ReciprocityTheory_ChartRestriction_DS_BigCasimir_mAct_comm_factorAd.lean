-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.BigCasimir.mAct_comm_factorAd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:24:27.34069+00:00
-- url     : https://prove2.me/submissions/ad0c8bbf-e26a-45e0-9cda-38649b6c3f3f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_big_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_mAct_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_factorAd_apply

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.BigCasimir
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir
theorem _root_.solution (k : ℕ) (i : Fin k) (a b c d : Fin n) :
    mAct E k a b * factorAd k i c d = factorAd k i c d * mAct E k a b := by
  ext F : 1
  refine big_ext fun κ => ?_
  simp only [Module.End.mul_apply, mAct_apply, factorAd_apply, map_sub]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS.BigCasimir
