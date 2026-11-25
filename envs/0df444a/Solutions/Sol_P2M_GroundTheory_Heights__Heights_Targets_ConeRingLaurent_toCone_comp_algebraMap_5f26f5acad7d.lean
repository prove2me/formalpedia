-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_toCone_comp_algebraMap_5f26f5acad7d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:29:21.42642+00:00
-- url     : https://prove2.me/submissions/4ec14d38-6094-4707-bd04-a439c8259f85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeRingLaurent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PConeRingLaurent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.Targets.ConeRingLaurent
variable {K : Type} [Fintype K] {ι : K → Type} (i : (k : K) → ι k)
namespace GroundTheory.Heights₂.Heights.Targets.ConeRingLaurent
theorem _root_.solution : (toCone i).comp (algebraMap (DehomRing i) (Laurent i)) = ratioMap i := by
  refine RingHom.ext fun y => ?_
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply (DehomRing i) (MvPolynomial K (DehomRing i)) (Laurent i),
    toCone, IsLocalization.Away.lift_eq, MvPolynomial.algebraMap_eq, laurentToConeRing, eval₂Hom_C]
end GroundTheory.Heights₂.Heights.Targets.ConeRingLaurent
