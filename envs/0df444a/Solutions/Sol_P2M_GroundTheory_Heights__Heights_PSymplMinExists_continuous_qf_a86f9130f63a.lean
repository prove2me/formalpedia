-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplMinExists_continuous_qf_a86f9130f63a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:46.687387+00:00
-- url     : https://prove2.me/submissions/34b90564-4b12-4953-b2da-e6f35411fe41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplMinExists

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
open GroundTheory.Heights₂.Heights.PSymplMinExists
variable {ι : Type} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.PSymplMinExists
theorem _root_.solution (G : Matrix ι ι ℝ) : Continuous (qf G) :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
end GroundTheory.Heights₂.Heights.PSymplMinExists
