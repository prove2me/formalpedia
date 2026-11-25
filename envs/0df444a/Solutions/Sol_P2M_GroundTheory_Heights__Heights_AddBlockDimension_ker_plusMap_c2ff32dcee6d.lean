-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockDimension_ker_plusMap_c2ff32dcee6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:00.794183+00:00
-- url     : https://prove2.me/submissions/9aec63cc-de10-4904-9d98-81df4f764fb5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicNew

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.AddBlockDimension
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}
  (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.AddBlockDimension
theorem _root_.solution : RingHom.ker (plusMap D) = D.extIdeal := rfl
end GroundTheory.Heights₂.Heights.AddBlockDimension
