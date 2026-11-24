-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.pDRho_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:19:42.287913+00:00
-- url     : https://prove2.me/submissions/93e95c43-411d-402d-958f-3290004ace98

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Unique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PrhoEntryHasDerivAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pDRho_apply

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
theorem _root_.solution (a b : Fin n) : pDRho ε β (Matrix.single a b 1) = pAdM ε β a b := by
  ext p q
  rw [pDRho_apply]
  simp only [pAdM, Matrix.single_apply, Matrix.one_apply]
  by_cases h1 : p.1.1 = a <;> by_cases h2 : q.1.1 = b <;> by_cases h3 : p.1.2 = q.1.2 <;>
    by_cases h4 : q.1.2 = a <;> by_cases h5 : p.1.2 = b <;> by_cases h6 : p.1.1 = q.1.1 <;>
    simp_all [eq_comm]
end ReciprocityTheory.ChartRestriction.DS.HW
