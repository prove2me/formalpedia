-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Rm_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:41:22.162808+00:00
-- url     : https://prove2.me/submissions/e1a8d5ee-f9cc-4913-a416-04a6becd3798

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_zetaC_pow_self

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
theorem _root_.solution {m : ℕ} (hm : 0 < m) {x : ℂ} (hx : x ∈ Rm m) : IsIntegral ℤ x := by
  have hζ : IsIntegral ℤ (zetaC m) :=
    IsIntegral.of_pow hm (by rw [zetaC_pow_self hm]; exact isIntegral_one)
  have hle : Rm m ≤ (integralClosure ℤ ℂ).toSubring :=
    Subring.closure_le.mpr (Set.singleton_subset_iff.mpr hζ)
  exact hle hx
end ReciprocityTheory.ChartRestriction.L1
