-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.BigCasimir.mAct_isGlRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:30:31.916265+00:00
-- url     : https://prove2.me/submissions/8bd56416-928b-4e21-bffa-bdb6b6fbc4c1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_big_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_mAct_apply

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
theorem _root_.solution (hE : IsGlRep E) (k : ℕ) : IsGlRep (mAct E k) := by
  intro a b c d
  ext F : 1
  refine big_ext fun κ => ?_
  have := LinearMap.congr_fun (hE a b c d) (F κ)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this ⊢
  split_ifs at this ⊢ <;> simpa [mAct_apply, PiLp.sub_apply] using this
end ReciprocityTheory.ChartRestriction.DS.BigCasimir
