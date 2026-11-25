-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.mAct_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:46.056461+00:00
-- url     : https://prove2.me/submissions/812262b0-7d52-4aa0-95a1-fdaad91245c7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_big_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mAct_apply

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
theorem _root_.solution (hE : IsGlRep E) (k : ℕ) (a b c d : Fin n) :
    mAct E k a b * mAct E k c d - mAct E k c d * mAct E k a b =
      (if b = c then mAct E k a d else 0) - (if d = a then mAct E k c b else 0) := by
  apply LinearMap.ext
  intro F
  apply big_ext
  intro κ
  have h := LinearMap.congr_fun (hE a b c d) (F κ)
  clear hE
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
    simp_all [mAct_apply, Module.End.mul_apply, PiLp.sub_apply]
end ReciprocityTheory.ChartRestriction.DS
