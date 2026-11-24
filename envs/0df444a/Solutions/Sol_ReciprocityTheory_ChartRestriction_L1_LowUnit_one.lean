-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.LowUnit.one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:35:12.160467+00:00
-- url     : https://prove2.me/submissions/71799f2d-4cac-452f-88fa-dc654b561915

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
namespace LowUnit
theorem _root_.solution (R : Subring ℂ) : LowUnit R 1 0 1 := by
  refine ⟨one_mem R, by rw [inv_one]; exact one_mem R, one_ne_zero,
    fun n hn => absurd hn (Nat.not_lt_zero n), ?_⟩
  simp
end LowUnit
end ReciprocityTheory.ChartRestriction.L1
