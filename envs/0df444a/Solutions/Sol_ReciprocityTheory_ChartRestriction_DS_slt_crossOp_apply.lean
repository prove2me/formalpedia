-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slt_crossOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:53.911829+00:00
-- url     : https://prove2.me/submissions/59f0674f-b6b0-4586-ba5c-28c8cb0f9a75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SltEqZeroOfCompact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_coord_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_mAct_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_positionAd_apply

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
theorem _root_.solution (k : ℕ) (i : Fin k) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    crossOp ε E k i F κ = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if (κ i).1 = a then E b a (F (Function.update κ i (b, (κ i).2))) else 0) -
        (if (κ i).2 = b then E b a (F (Function.update κ i ((κ i).1, a))) else 0)) := by
  rw [← slt_coord_apply k κ (crossOp ε E k i F)]
  simp only [crossOp, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [slt_coord_apply]
  change factorAd k i a b (mAct E k b a F) κ = _
  rw [slt_positionAd_apply, slt_mAct_apply, slt_mAct_apply]
end ReciprocityTheory.ChartRestriction.DS
