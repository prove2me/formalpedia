-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.rtr_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:09.329886+00:00
-- url     : https://prove2.me/submissions/9c12f63b-83bf-40ec-9ea0-b149da3b755c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelSpace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_rtr_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    rtr ε k f ∈ Vsp ε m := by
  have h : Vsp ε m ≤ (Vsp ε m).comap (rtr ε k) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k', rfl⟩
    show rtr ε k (rtr ε k' (f0K ε m)) ∈ Vsp ε m
    rw [← rtr_mul]
    exact Submodule.subset_span ⟨k * k', rfl⟩
  exact h hf
end ReciprocityTheory.ChartRestriction.DS.HW
