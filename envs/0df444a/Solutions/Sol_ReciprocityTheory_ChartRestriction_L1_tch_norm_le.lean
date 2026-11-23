-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.tch_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:53.456528+00:00
-- url     : https://prove2.me/submissions/e3dcdd41-61ef-4435-8249-4421876a2ce6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormNatCastClOfNotDvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_muP_norm

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
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {ξ : ℂ_[l]} (hξ : ξ ∈ Tch l) : ‖ξ‖ ≤ 1 := by
  rcases hξ with rfl | h
  · simp
  · exact (muP_norm l h).le
end ReciprocityTheory.ChartRestriction.L1
