-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Om_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:00:10.194714+00:00
-- url     : https://prove2.me/submissions/1bff84a5-d932-4852-962c-b62bcf48b5e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (d : ℕ) (x : Om d) : IsAlgebraic ℚ (x : ℂ) := by
  have hx : IsIntegral (KQ d) (x : ℂ) := x.2
  exact (isIntegral_trans (R := ℚ) _ hx).isAlgebraic
end ReciprocityTheory.ChartRestriction.L1
