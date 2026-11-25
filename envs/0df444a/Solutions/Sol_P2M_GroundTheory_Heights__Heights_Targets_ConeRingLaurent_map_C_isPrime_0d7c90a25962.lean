-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_map_C_isPrime_0d7c90a25962
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:29:46.909847+00:00
-- url     : https://prove2.me/submissions/149b26f6-0e0f-4f75-ae8a-506c9482c84e

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
namespace GroundTheory.Heights₂.Heights.Targets.ConeRingLaurent
theorem _root_.solution {D σ : Type*} [CommRing D] (𝔮 : Ideal D) [𝔮.IsPrime] :
    (𝔮.map (C : D →+* MvPolynomial σ D)).IsPrime := by
  rw [← Ideal.mk_ker (I := 𝔮), ← MvPolynomial.ker_map]
  exact RingHom.ker_isPrime _
end GroundTheory.Heights₂.Heights.Targets.ConeRingLaurent
