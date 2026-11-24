-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetAug_comp_jetBC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:21.821648+00:00
-- url     : https://prove2.me/submissions/3a17f636-491f-4a73-927a-f4f9827f5d04

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
theorem _root_.solution (κ : Type) (m : ℕ) :
    (jetAug : Jet S' κ m →ₐ[S'] S').toRingHom.comp (jetBC ψ κ m) = ψ.comp (jetAug : Jet S κ m →ₐ[S] S).toRingHom := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)) <;>
    simp [jetBC, jetAug, liftJet]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
