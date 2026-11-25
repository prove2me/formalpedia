-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussDualMin_inner_toLp_eq_dotProduct_e8491acdea74
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:53.951042+00:00
-- url     : https://prove2.me/submissions/0b63b2e5-640a-42d7-ae55-4192306b678e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussDualMin

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
open Matrix
open GroundTheory.Heights₂.Heights.PGaussDualMin
namespace GroundTheory.Heights₂.Heights.PGaussDualMin
theorem _root_.solution {g : ℕ} (m w : Fin g → ℝ) :
    inner ℝ (WithLp.toLp 2 m : EuclideanSpace ℝ (Fin g)) (WithLp.toLp 2 w) = m ⬝ᵥ w := by
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
end GroundTheory.Heights₂.Heights.PGaussDualMin
