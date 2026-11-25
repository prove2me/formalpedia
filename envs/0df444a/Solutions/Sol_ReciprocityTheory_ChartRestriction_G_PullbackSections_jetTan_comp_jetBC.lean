-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetTan_comp_jetBC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:27:05.656198+00:00
-- url     : https://prove2.me/submissions/ac96445c-6a70-4603-b1c0-11a192f5ee2a

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
theorem _root_.solution {κ : Type} [DecidableEq κ] (ℓ : κ) (m : ℕ) :
    (jetTan ℓ : Jet S' κ (m + 1) →ₐ[S'] DualNumber S').toRingHom.comp (jetBC ψ κ (m + 1)) =
      (dualMap ψ).comp (jetTan ℓ : Jet S κ (m + 1) →ₐ[S] DualNumber S).toRingHom := by
  have e : ∀ (T : Type) [CommRing T] (P : MvPolynomial κ T),
      (jetTan ℓ : Jet T κ (m + 1) →ₐ[T] DualNumber T) (Ideal.Quotient.mk (orig T κ ^ (m + 1 + 1)) P) =
        aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber T) else 0) P := fun _ _ _ => rfl
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, jetBC_mk, e, aeval_C,
      MvPolynomial.map_C]
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, jetBC_mk, e, aeval_X,
      MvPolynomial.map_X]
    split_ifs <;> ext <;> simp [dualMap]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
