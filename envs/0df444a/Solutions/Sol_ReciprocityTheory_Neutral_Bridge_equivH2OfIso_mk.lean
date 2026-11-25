-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.equivH2OfIso_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:45:13.138181+00:00
-- url     : https://prove2.me/submissions/baaf9fe3-2348-4d23-a8f1-e86340518497

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
variable {R : Type*} [CommRing R]
  {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  (e : H ≃ₜ* G) (rho : Representation R G M) (rho' : Representation R H M)
  (hc : ∀ h m, rho (e h) m = rho' h m)
namespace ReciprocityTheory.Neutral.Bridge
theorem _root_.solution (f : Z2 rho) : equivH2OfIso e rho rho' hc (Submodule.Quotient.mk f) =
    Submodule.Quotient.mk (compatiblePairCocycles2 rho rho' (e : H →* G) (continuous_coe_iso e) LinearMap.id
      continuous_id hc f) := rfl
end ReciprocityTheory.Neutral.Bridge
