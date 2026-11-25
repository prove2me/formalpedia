-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RatPrimeDense_continuous_aeval_9170a0851d8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:35.361878+00:00
-- url     : https://prove2.me/submissions/a87e115a-8345-468d-b7a9-cf2f323a1582

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRatPrimeDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiniteSeparatingModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsBounded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolyNonvanishDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRatPrimeDense

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
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace RatPrimeDense
theorem _root_.solution {σ : Type} (g : MvPolynomial σ ℚ) :
    Continuous fun z : σ → ℂ => aeval z g := by
  simp_rw [aeval_def, ← eval_map]
  exact MvPolynomial.continuous_eval _
end RatPrimeDense
end GroundTheory.Heights₂.Heights.HilbertSamuel
