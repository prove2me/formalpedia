-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_scale_inGroup_apply_of_ne_6de922e60143
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:36.626489+00:00
-- url     : https://prove2.me/submissions/4686fa25-50e1-47eb-a4aa-64a211c9344c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere

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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (i a : Fin k) (ha : a ≠ i) (c : ℂ) (u : Fin k × Fin n → ℂ) (j : Fin n) :
    scaleP (inGroup i) c u (a, j) = u (a, j) := by
  simp [scaleP, inGroup, ha]
end GroundTheory.Heights₂.Heights.LogInt
