-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_finrank_integers_770829070650
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:02:34.430168+00:00
-- url     : https://prove2.me/submissions/e4ba139f-8f48-4a92-aefc-ba4237cb8796

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_BaseChangeIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField TensorProduct
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution : Module.finrank (𝓞 K) (𝓞 L) = Module.finrank K L :=
  (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L).symm
end GroundTheory.Heights₂.Heights.LatticeLemmas
