-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.smul_SL_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:40:49.454717+00:00
-- url     : https://prove2.me/submissions/a48b0d64-1242-4247-b96c-65a18febc680

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFacSlash
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_denom_SL_coe

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
theorem _root_.solution (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ)) /
      (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) := by
  first
  | (rw [UpperHalfPlane.coe_smul, UpperHalfPlane.num, denom_SL_coe]; simp)
  | (rw [UpperHalfPlane.specialLinearGroup_apply]; simp)
  | simp [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom]
end ReciprocityTheory.ChartRestriction.L1
