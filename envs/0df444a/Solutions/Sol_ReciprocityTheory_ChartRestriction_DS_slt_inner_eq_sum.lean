-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slt_inner_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:45.882304+00:00
-- url     : https://prove2.me/submissions/caa99c81-5e08-47ac-a06e-b75f022c8a7b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SltEqZeroOfCompact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_sum_fin_one_fun

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {k : ℕ} (i : Fin k) (A B : Big n k M) :
    inner ℂ A B = ∑ r, inner ℂ (slt i r A) (slt i r B) := by
  rw [PiLp.inner_apply, ← (slRest i).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [PiLp.inner_apply]
  exact (slt_sum_fin_one_fun
    (fun p => inner ℂ (A ((slRest i).symm (p, r))) (B ((slRest i).symm (p, r))))).symm
end ReciprocityTheory.ChartRestriction.DS
