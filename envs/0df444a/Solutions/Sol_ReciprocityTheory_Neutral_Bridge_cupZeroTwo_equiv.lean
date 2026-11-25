-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.cupZeroTwo_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:30:32.452874+00:00
-- url     : https://prove2.me/submissions/dfe710de-254c-4900-9919-6bf6290b1d07

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open ReciprocityTheory.Gal
variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {G G' : Type}
  [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (e : G ≃ₜ* G') (χ : G' →* Rˣ) (rho : Representation R G' M)
namespace ReciprocityTheory.Neutral.Bridge
theorem _root_.solution (m : H0 (rho.comp (MonoidHom.id G')))
    (y : H2 ((twDual χ rho).comp (MonoidHom.id G'))) :
    cupH0H2TwistedDual (χ.comp (e : G →* G')) (rho.comp (e : G →* G')) (MonoidHom.id G)
        (equivH0OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
          (fun _ _ => rfl) m)
        (equivH2OfIso e _ _ (twDual_compat e χ rho) y) =
      equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl)
        (cupH0H2TwistedDual χ rho (MonoidHom.id G') m y) := by
  induction y using Submodule.Quotient.induction_on with
  | _ y => rfl
end ReciprocityTheory.Neutral.Bridge
