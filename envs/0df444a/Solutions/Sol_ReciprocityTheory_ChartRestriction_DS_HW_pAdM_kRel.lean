-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.pAdM_kRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:27:25.479485+00:00
-- url     : https://prove2.me/submissions/266c5e61-0ab3-4d07-9d40-2fcc6df91afe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Unique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PrhoEntryHasDerivAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pDRho_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pDRho_bracket
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_prho_single_bracket
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_single_mul_Jm


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
theorem _root_.solution : Formalism.REAL.KRel ε (pAdM ε β) := by
  intro a b c d hab hcd
  have e : ∀ a b, pAdM ε β a b = pDRho ε β (Matrix.single a b 1) := fun a b => (pDRho_single ε β a b).symm
  simp only [e]
  rw [pDRho_bracket ε β (single_mul_Jm hab 1) (single_mul_Jm hcd 1), prho_single_bracket]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS.HW
