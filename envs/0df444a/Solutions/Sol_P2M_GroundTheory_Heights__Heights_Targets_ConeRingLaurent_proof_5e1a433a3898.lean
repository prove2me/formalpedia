-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_proof_5e1a433a3898
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:11:05.36988+00:00
-- url     : https://prove2.me/submissions/d324dcd1-5612-491a-8b7c-9c0d557291d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeRingLaurent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PConeRingLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_toCone_comp_algebraMap_5f26f5acad7d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_map_laurent_isPrime_940573875bd7

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
namespace GroundTheory.Heights₂.Heights.Targets
namespace ConeRingLaurent
theorem _root_.solution : ConeRingLaurent.Statement := by
  intro K _ ι i
  have hcomp : ratioMap i = (ConeRingLaurent.laurentEquiv i : ConeRingLaurent.Laurent i →+* ConeRing i).comp
      (algebraMap (DehomRing i) (ConeRingLaurent.Laurent i)) :=
    (ConeRingLaurent.toCone_comp_algebraMap i).symm
  constructor
  · rw [hcomp]
    refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (ConeRingLaurent.laurentEquiv i).bijective)
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  · intro 𝔮 h𝔮
    rw [hcomp, ← Ideal.map_map]
    have := ConeRingLaurent.map_laurent_isPrime i 𝔮
    exact Ideal.map_isPrime_of_equiv (ConeRingLaurent.laurentEquiv i)
end ConeRingLaurent
end GroundTheory.Heights₂.Heights.Targets
