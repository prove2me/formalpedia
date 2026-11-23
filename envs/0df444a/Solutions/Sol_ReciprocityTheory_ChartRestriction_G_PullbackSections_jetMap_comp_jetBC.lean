-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetMap_comp_jetBC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:31.588693+00:00
-- url     : https://prove2.me/submissions/4759a724-4d47-465a-ad1c-89c51eced11e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetBC_mk

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
theorem _root_.solution {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (hφ : ∀ i, φ i ∈ orig S κ')
    (hφ' : ∀ i, MvPolynomial.map ψ (φ i) ∈ orig S' κ') :
    (jetMap (m := m) (fun i => MvPolynomial.map ψ (φ i)) hφ').toRingHom.comp (jetBC ψ κ m) =
      (jetBC ψ κ' m).comp (jetMap (m := m) φ hφ).toRingHom := by
  have e : ∀ (T : Type) [CommRing T] (χ : κ → MvPolynomial κ' T) (hχ : ∀ i, χ i ∈ orig T κ')
      (P : MvPolynomial κ T), (jetMap (m := m) χ hχ) (Ideal.Quotient.mk (orig T κ ^ (m + 1)) P) =
        Ideal.Quotient.mk (orig T κ' ^ (m + 1)) (aeval χ P) := fun _ _ _ _ _ => rfl
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)) <;>
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, jetBC_mk, e, aeval_C, aeval_X,
      MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.algebraMap_eq]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
