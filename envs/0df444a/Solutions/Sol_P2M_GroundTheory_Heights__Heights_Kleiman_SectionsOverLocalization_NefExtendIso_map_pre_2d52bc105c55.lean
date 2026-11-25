-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_map_pre_2d52bc105c55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:56:22.727326+00:00
-- url     : https://prove2.me/submissions/842f2642-945b-4c23-8652-04ad7d3a3f6e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefExtendIsoSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefExtendIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
variable {S : Type} [CommRing S] {F : Type} [Field F] [Algebra S F] {Ω : Type} [Field Ω] [Algebra S Ω]
  [Algebra F Ω] [IsScalarTower S F Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
theorem _root_.solution (hφ : Function.Bijective (algebraMap S F)) (f : Kleiman.Poly F N) :
    map (algebraMap S F) (map ((RingEquiv.ofBijective _ hφ).symm : F →+* S) f) = f := by
  have hc : (algebraMap S F).comp ((RingEquiv.ofBijective _ hφ).symm : F →+* S) = RingHom.id F :=
    RingHom.ext fun y => (RingEquiv.ofBijective _ hφ).apply_symm_apply y
  rw [map_map, hc, map_id]
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
