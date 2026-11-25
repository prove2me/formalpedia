-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kq_int_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:51:30.43955+00:00
-- url     : https://prove2.me/submissions/c15dfe12-8874-40e5-a29d-69ab04a49560

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormSqrtNegPowPrimeSqSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_int_le

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
theorem _root_.solution (n : ℤ) (h : (l : ℤ) ∣ n) : ‖(n : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨m, rfl⟩ := h
  push_cast
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (kq_int_le l m)
end ReciprocityTheory.ChartRestriction.L1
