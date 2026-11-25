-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.map_sub_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:27:21.365743+00:00
-- url     : https://prove2.me/submissions/524797b5-003e-4cdd-b549-740b1e304077

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
theorem _root_.solution {κ : Type} (P : MvPolynomial κ S) :
    MvPolynomial.map ψ (P - C (MvPolynomial.constantCoeff P)) =
      MvPolynomial.map ψ P - C (MvPolynomial.constantCoeff (MvPolynomial.map ψ P)) := by
  simp [MvPolynomial.constantCoeff_map]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
