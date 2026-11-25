-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.AA_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:05.270403+00:00
-- url     : https://prove2.me/submissions/dd737ea2-b227-4f9c-b42d-52c553348fca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_isMF_AA
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
theorem _root_.solution (γ : SL(2, ℤ)) (τ : ℍ) : AA (γ • τ) = denom γ τ ^ 12 * AA τ := by
  exact isMF_AA.smul_eq γ τ
end ReciprocityTheory.ChartRestriction.L1
