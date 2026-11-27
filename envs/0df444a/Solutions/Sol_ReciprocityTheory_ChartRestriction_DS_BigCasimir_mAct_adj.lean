-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.BigCasimir.mAct_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:24:24.526237+00:00
-- url     : https://prove2.me/submissions/49533d18-0d20-4a31-8754-0bdfae9cc4ed

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
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
theorem _root_.solution (hU : IsInfUnitary ε E) (k : ℕ) {a b : Fin n} (hab : ε a = ε b) (F G : Big n k M) :
    inner ℂ (mAct E k a b F) G = inner ℂ F (mAct E k b a G) := by
  simp only [PiLp.inner_apply, mAct_apply, hU a b, adjSign, hab, if_true, one_mul]
end ReciprocityTheory.ChartRestriction.DS.BigCasimir
