-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplMinExists_qf_smul_c52cc2b03309
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:02.84506+00:00
-- url     : https://prove2.me/submissions/74e3c1d8-c0c6-47d2-9fd5-67274e6b95b4

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
theorem _root_.solution (G : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) : qf G (c • x) = c ^ 2 * qf G x := by
  simp only [qf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring
end GroundTheory.Heights₂.Heights.PSymplMinExists
