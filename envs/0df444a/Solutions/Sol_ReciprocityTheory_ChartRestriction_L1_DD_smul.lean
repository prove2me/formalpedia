-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.DD_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:08.695283+00:00
-- url     : https://prove2.me/submissions/2b934a7f-d4e4-4afa-bf0e-2c996fa8b986

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_isMF_DD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_smul_eq

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
theorem _root_.solution (γ : SL(2, ℤ)) (τ : ℍ) : DD (γ • τ) = denom γ τ ^ 12 * DD τ := by
  exact isMF_DD.smul_eq γ τ
end ReciprocityTheory.ChartRestriction.L1
