-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kmu_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:35:12.759397+00:00
-- url     : https://prove2.me/submissions/99254c23-d899-45c5-a46a-f8022ae642ed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FrobFixNegOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormNatCastClOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsPowerMulUnitNorm

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
theorem _root_.solution {x : ℂ_[l]} (hx : x ∈ Kmu l) :
    ∃ a ∈ Rmu l, ∃ b ∈ Rmu l, b ≠ 0 ∧ x = a / b := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.1 hx
  by_cases hz0 : z = 0
  · refine ⟨0, (Rmu l).zero_mem, 1, (Rmu l).one_mem, one_ne_zero, ?_⟩
    rw [hz0, div_zero, zero_div]
  · exact ⟨y, hy, z, hz, hz0, rfl⟩
end ReciprocityTheory.ChartRestriction.L1
