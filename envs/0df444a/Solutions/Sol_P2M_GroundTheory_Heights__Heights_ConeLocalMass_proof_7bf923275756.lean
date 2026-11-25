-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeLocalMass_proof_7bf923275756
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:53:51.499106+00:00
-- url     : https://prove2.me/submissions/6b549577-3a4d-4d40-8609-54472be47f31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFiniteFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_hausdorffMeasure_coneSet_ball_le_b81ecaae35f7

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
open MvPolynomial MeasureTheory
open scoped ENNReal NNReal
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace ConeLocalMass
theorem _root_.solution (hDim : ConeFiniteFibreDim.Statement) (hMass : MassFinite.Statement)
    (hNull : NullSmaller.Statement) : ConeLocalMass.Statement := by
  intro n m h J hJ hm hmn hfib R
  have hle := hDim n m h J hJ hm hmn hfib
  refine lt_of_le_of_lt (hausdorffMeasure_coneSet_ball_le h J m R) ?_
  refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top) ?_
  rcases hle.lt_or_eq with hlt | heq
  · rw [measure_mono_null Set.inter_subset_left (hNull n m J hlt)]
    exact ENNReal.zero_lt_top
  · exact hMass n m J hJ.isPrime heq _
end ConeLocalMass
end GroundTheory.Heights₂.Heights
