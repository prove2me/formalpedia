-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointLine_eval_pairing_f70de561052b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:46.16945+00:00
-- url     : https://prove2.me/submissions/4d05f3d1-bb7f-4982-8f6f-a768dbdf4ea4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine

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
open GroundTheory.Heights₂.Heights.PointLine
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.PointLine
theorem _root_.solution (y : Fin n → ℂ) (u : Fin 1 × Fin n → ℂ) :
    eval u (pairing y) = ∑ j, y j * u (0, j) := by
  simp [pairing]
end GroundTheory.Heights₂.Heights.PointLine
