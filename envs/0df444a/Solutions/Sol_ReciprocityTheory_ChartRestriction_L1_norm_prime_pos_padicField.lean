-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_prime_pos_padicField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:53:22.540051+00:00
-- url     : https://prove2.me/submissions/9471ea0b-61a0-4df7-b417-e021377eba5b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_l_Cl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : 0 < ‖(l : ℂ_[l])‖ := by
  rw [norm_l_Cl]
  exact inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos)
end ReciprocityTheory.ChartRestriction.L1
