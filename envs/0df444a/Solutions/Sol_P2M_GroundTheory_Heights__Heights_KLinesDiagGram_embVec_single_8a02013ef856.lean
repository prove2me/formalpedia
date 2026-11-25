-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesDiagGram_embVec_single_8a02013ef856
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:00:44.900644+00:00
-- url     : https://prove2.me/submissions/cfe5dacb-d498-485b-9788-edf075fd871e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesDiagGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KLinesDiagGram
namespace GroundTheory.Heights₂.Heights.KLinesDiagGram
theorem _root_.solution {K : Type*} [Field K] (σ : K →+* ℂ) {n : ℕ} (x : Fin n) :
    embVec σ (Pi.single x 1 : Fin n → K) = Pi.single x 1 := by
  funext y
  simp only [embVec, Pi.single_apply]
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.KLinesDiagGram
