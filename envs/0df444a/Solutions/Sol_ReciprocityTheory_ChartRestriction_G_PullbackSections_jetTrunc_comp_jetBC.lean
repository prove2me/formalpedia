-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetTrunc_comp_jetBC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:33:22.854621+00:00
-- url     : https://prove2.me/submissions/276afd43-0adf-41a2-84ff-edee88b39201

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
    (jetTrunc : Jet S' κ (m + 1) →ₐ[S'] Jet S' κ m).toRingHom.comp (jetBC ψ κ (m + 1)) =
      (jetBC ψ κ m).comp (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m).toRingHom := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)) <;>
    simp [jetBC, jetTrunc]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
