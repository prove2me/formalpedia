-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slt_positionAd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:49.479347+00:00
-- url     : https://prove2.me/submissions/4ec3c3cd-9844-43f5-b472-556830db58d5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SltEqZeroOfCompact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_ofCoords_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_coord_apply

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
theorem _root_.solution (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    factorAd k i a b F κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  rw [factorAd, slt_ofCoords_apply, LinearMap.sub_apply]
  split_ifs <;> simp [slt_coord_apply]
end ReciprocityTheory.ChartRestriction.DS
