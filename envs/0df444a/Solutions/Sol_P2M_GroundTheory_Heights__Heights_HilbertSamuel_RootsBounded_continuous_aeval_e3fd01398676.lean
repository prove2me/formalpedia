-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsBounded_continuous_aeval_e3fd01398676
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:40.525008+00:00
-- url     : https://prove2.me/submissions/e003f28d-32b3-4403-a4d7-5fb3539a429d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsBounded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRootsBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Filter Topology NNReal
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace RootsBounded
theorem _root_.solution {e : ℕ} (g : MvPolynomial (Fin e) ℚ) :
    Continuous fun y : Fin e → ℂ => aeval y g := by
  have h := MvPolynomial.continuous_eval (p := MvPolynomial.map (algebraMap ℚ ℂ) g)
  refine h.congr fun y => ?_
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
end RootsBounded
end GroundTheory.Heights₂.Heights.HilbertSamuel
