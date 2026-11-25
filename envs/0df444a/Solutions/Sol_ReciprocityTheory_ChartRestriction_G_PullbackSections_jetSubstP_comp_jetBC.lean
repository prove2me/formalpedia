-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetSubstP_comp_jetBC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:55.091277+00:00
-- url     : https://prove2.me/submissions/c2d985b8-5f2e-49d5-95dc-bfb9bfb61d32

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetBC_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_map_sub_const

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
theorem _root_.solution {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) :
    (jetSubstP m (fun i => MvPolynomial.map ψ (φ i)) : Jet S' κ m →ₐ[S'] Jet S' κ' m).toRingHom.comp (jetBC ψ κ m) =
      (jetBC ψ κ' m).comp (jetSubstP m φ : Jet S κ m →ₐ[S] Jet S κ' m).toRingHom := by
  have e : ∀ (T : Type) [CommRing T] (χ : κ → MvPolynomial κ' T) (hχ : ∀ i, χ i ∈ orig T κ')
      (P : MvPolynomial κ T), (jetMap (m := m) χ hχ) (Ideal.Quotient.mk (orig T κ ^ (m + 1)) P) =
        Ideal.Quotient.mk (orig T κ' ^ (m + 1)) (aeval χ P) := fun _ _ _ _ _ => rfl
  unfold jetSubstP
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)) <;>
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, jetBC_mk, e, aeval_C, aeval_X,
      MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.algebraMap_eq, map_sub_const]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
