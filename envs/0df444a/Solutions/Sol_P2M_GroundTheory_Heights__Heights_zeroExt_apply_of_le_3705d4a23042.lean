-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_zeroExt_apply_of_le_3705d4a23042
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:40.903905+00:00
-- url     : https://prove2.me/submissions/65554cff-b20a-4fd0-bf20-76dd29cc78f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre

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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m k : ℕ} (x : EuclideanSpace ℂ (Fin m)) (j : Fin (m + k))
    (hj : m ≤ (j : ℕ)) : zeroExt m k x j = 0 := by
  revert hj
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · intro hi
    simp at hi
    omega
  · intro _
    simp [zeroExt]
end GroundTheory.Heights₂.Heights
