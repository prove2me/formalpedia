-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.cupOneOne_equivH1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:38:50.970858+00:00
-- url     : https://prove2.me/submissions/fcb7903b-5554-4860-81d0-2590fe53e8f1

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
theorem _root_.solution (hr : ContAction (rho.comp (MonoidHom.id G')))
    (hr' : ContAction ((rho.comp (e : G →* G')).comp (MonoidHom.id G)))
    (y : H1 ((twDual χ rho).comp (MonoidHom.id G'))) (x : H1 (rho.comp (MonoidHom.id G'))) :
    cupH1H1TwistedDual (χ.comp (e : G →* G')) (rho.comp (e : G →* G')) (MonoidHom.id G) hr'
        (equivH1OfIso e _ _ (twDual_compat e χ rho) y)
        (equivH1OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
          (fun _ _ => rfl) x) =
      equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl)
        (cupH1H1TwistedDual χ rho (MonoidHom.id G') hr y x) := by
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
end ReciprocityTheory.Neutral.Bridge
