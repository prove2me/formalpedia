-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eq_zeroExt_of_a65a279d9723
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:56.687286+00:00
-- url     : https://prove2.me/submissions/dc66e39a-b6a5-4f88-91d7-a6cb8afb45ec

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
theorem _root_.solution {m k : ℕ} {y : EuclideanSpace ℂ (Fin (m + k))}
    (hy : ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0) :
    y = zeroExt m k (WithLp.toLp 2 fun i => y (Fin.castAdd k i)) := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [zeroExt]
  · simp [zeroExt, hy (Fin.natAdd m i) (by simp)]
end GroundTheory.Heights₂.Heights
