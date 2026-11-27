-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.jT_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:28:00.733173+00:00
-- url     : https://prove2.me/submissions/7ca8d614-ef13-4f2a-aada-8ddbb5565ebd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_AA_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_DD_smul

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
theorem _root_.solution (γ : SL(2, ℤ)) (τ : ℍ) : jT (γ • τ) = jT τ := by
  unfold jT
  rw [AA_smul, DD_smul, mul_div_mul_left _ _ (pow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ τ))]
end ReciprocityTheory.ChartRestriction.L1
