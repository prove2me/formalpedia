-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplReduceMem_omega_sub_smul_c8100a0683da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:21.823799+00:00
-- url     : https://prove2.me/submissions/fd421c37-7d68-444d-a80a-aea61c61296b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplReduceMem

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
open GroundTheory.Heights₂.Heights.PSymplReduceMem
namespace GroundTheory.Heights₂.Heights.PSymplReduceMem
theorem _root_.solution {l : Type} [Fintype l] [DecidableEq l] (u v w : l ⊕ l → ℝ) (c d : ℝ) :
    symplOmega (u - c • w) (v - d • w) =
      symplOmega u v - d * symplOmega u w - c * symplOmega w v + c * d * symplOmega w w := by
  unfold symplOmega
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring
end GroundTheory.Heights₂.Heights.PSymplReduceMem
