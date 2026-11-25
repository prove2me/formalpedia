-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_X_sub_C_mem_ker_2ebe1b0d4571
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:24:57.063095+00:00
-- url     : https://prove2.me/submissions/dfca7372-ccf9-48d4-8fd6-78e0768e9f36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff

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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (p : Fin n → ℂ) (j : Fin n) :
    X j - C (p j) ∈ RingHom.ker (eval p) := by
  simp [RingHom.mem_ker]
end GroundTheory.Heights₂.Heights
