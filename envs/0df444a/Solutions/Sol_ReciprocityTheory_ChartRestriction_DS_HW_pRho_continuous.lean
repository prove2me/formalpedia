-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.pRho_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:12:43.915253+00:00
-- url     : https://prove2.me/submissions/17ae21aa-e1ee-4472-a13a-825243c9d53e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Unique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PrhoEntryHasDerivAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pRho_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_continuous_toM


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open scoped Kronecker
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
variable {ε : Fin n → Bool} {β : Bool}
variable (ε β)
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution :
    Continuous (fun k : KG ε =>
      ((pRho ε β k : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ)) := by
  have hm : Continuous (fun k : KG ε => toMK k) := (continuous_toM ε).comp continuous_subtype_val
  refine continuous_matrix fun p q => ?_
  simp only [pRho_apply]
  exact (hm.matrix_elem _ _).mul ((hm.matrix_elem _ _).star)
end ReciprocityTheory.ChartRestriction.DS.HW
