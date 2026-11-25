-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.homS_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:53:07.483811+00:00
-- url     : https://prove2.me/submissions/a5460660-d316-45d1-b4c0-d0caf3ba383e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProjA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable {K : Type} [Field K] (U : PowerSeries K)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (m : ℕ) : homS U m (0 : K[X]) = 0 := by
  simp [homS]
end ReciprocityTheory.ChartRestriction.L1
