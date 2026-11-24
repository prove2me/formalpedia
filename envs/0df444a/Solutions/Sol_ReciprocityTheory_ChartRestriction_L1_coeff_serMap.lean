-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.coeff_serMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:08:23.03923+00:00
-- url     : https://prove2.me/submissions/5fd59cfe-7ded-4c43-bbf5-9b09cb187134

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProjA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProj

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
variable {E : Type} [Field E]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (ψ : E →+ E) (S : PowerSeries E) (n : ℕ) :
    PowerSeries.coeff n (serMap ψ S) = ψ (PowerSeries.coeff n S) := by
  simp [serMap]
end ReciprocityTheory.ChartRestriction.L1
