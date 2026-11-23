-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetBC_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:41.753018+00:00
-- url     : https://prove2.me/submissions/891cdd42-516c-43f7-8eb4-abbb9368c412

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
theorem _root_.solution {κ : Type} {m : ℕ} (P : MvPolynomial κ S) :
    jetBC ψ κ m (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ (MvPolynomial.map ψ P) := rfl
end ReciprocityTheory.ChartRestriction.G.PullbackSections
