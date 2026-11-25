-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.DualityFor.of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:55:46.805864+00:00
-- url     : https://prove2.me/submissions/de210168-d14e-4bfc-9306-e9688deb5d0a

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_Transport
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_bijective_flip_of_iso
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_bijective_of_iso
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_cupOneOne_equivH1
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_cupTwoZero_equiv
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_cupZeroTwo_equiv


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
variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
namespace ReciprocityTheory.Neutral.Bridge
namespace DualityFor
theorem _root_.solution (e : G ≃ₜ* G') (χ : G' →* Rˣ) {rho : Representation R G' M} (hrho : ContAction rho)
    (h : DualityFor (χ.comp (e : G →* G')) (rho.comp (e : G →* G')) (contAction_comp e hrho)) :
    DualityFor χ rho hrho := by
  obtain ⟨⟨h0⟩, h1, h2, h3, h4⟩ := h
  refine ⟨⟨(equivH2OfIso e (charRep χ) (charRep (χ.comp (e : G →* G'))) (fun _ _ => rfl)).trans h0⟩,
    ?_, ?_, ?_, ?_⟩
  · exact bijective_of_iso
      (equivH0OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
        (fun _ _ => rfl))
      (equivH2OfIso e _ _ (twDual_compat e χ rho))
      (equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl))
      _ _ (cupZeroTwo_equiv e χ rho) h1
  · exact bijective_of_iso
      (equivH1OfIso e _ _ (twDual_compat e χ rho))
      (equivH1OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
        (fun _ _ => rfl))
      (equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl))
      _ _ (cupOneOne_equivH1 e χ rho _ _) h2
  · exact bijective_flip_of_iso
      (equivH1OfIso e _ _ (twDual_compat e χ rho))
      (equivH1OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
        (fun _ _ => rfl))
      (equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl))
      _ _ (cupOneOne_equivH1 e χ rho _ _) h3
  · exact bijective_of_iso
      (equivH2OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
        (fun _ _ => rfl))
      (equivH0OfIso e _ _ (twDual_compat e χ rho))
      (equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl))
      _ _ (cupTwoZero_equiv e χ rho) h4
end DualityFor
end ReciprocityTheory.Neutral.Bridge
