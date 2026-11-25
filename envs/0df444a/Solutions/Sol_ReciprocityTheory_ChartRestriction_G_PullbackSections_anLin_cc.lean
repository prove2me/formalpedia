-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.anLin_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:59:51.081901+00:00
-- url     : https://prove2.me/submissions/d4b28134-0e32-4d33-9633-623c2cefe434

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anLin_coe

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
theorem _root_.solution (A : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (p : Fin 1 × Fin g) :
    MvPowerSeries.constantCoeff ((anLin A p : MvPolynomial (Fin 1 × Fin g') ℂ) : MvPowerSeries (Fin 1 × Fin g') ℂ) = 0 := by
  rw [anLin_coe, map_sum]
  simp
end ReciprocityTheory.ChartRestriction.G.PullbackSections
