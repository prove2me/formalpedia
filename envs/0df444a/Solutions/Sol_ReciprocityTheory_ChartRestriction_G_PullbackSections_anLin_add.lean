-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.anLin_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:43:20.708777+00:00
-- url     : https://prove2.me/submissions/1d274efc-edb2-4855-b7ca-58bd17b24d85

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {g g' : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (A B : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (p : Fin 1 × Fin g) :
    anLin (A + B) p = anLin A p + anLin B p := by
  simp [anLin, add_mul, Finset.sum_add_distrib]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
