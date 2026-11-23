-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetBC_psJet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:58.477862+00:00
-- url     : https://prove2.me/submissions/893166c8-437c-471c-bd76-d5cb277b997c

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC

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
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S) :
    jetBC ψ κ m (psJet m f) = psJet m (MvPowerSeries.map ψ f) := by
  simp [jetBC, psJet, psTrunc, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
