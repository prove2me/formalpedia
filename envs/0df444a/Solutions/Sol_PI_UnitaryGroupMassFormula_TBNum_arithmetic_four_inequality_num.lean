-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TBNum.arithmetic_four_inequality_num
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:43:45.857646+00:00
-- url     : https://prove2.me/submissions/f311a361-d2cc-4d80-bbf8-d058ad4125ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ScaledBoundInequalityHypothesesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_SchwarzBallNumerics_ArithmeticFourInequalityNum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TBNum
open ComplexConjugate
namespace PI.UnitaryGroupMassFormula.TBNum
theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.TB.ScaledBoundInequality := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.ScaledBoundInequality
  intro P lNc D L G2 G1 hP hl hD hL hG2 hG1
  have hD0 : D ≠ 0 := by linarith
  have hcan : 2 * lNc / D * D = 2 * lNc := div_mul_cancel₀ _ hD0
  have hexp : (5 * P + 2 * lNc / D) * D * L = 5 * P * D * L + 2 * lNc * L := by
    calc (5 * P + 2 * lNc / D) * D * L = 5 * P * D * L + (2 * lNc / D * D) * L := by ring
      _ = 5 * P * D * L + 2 * lNc * L := by rw [hcan]
  rw [hexp]
  have h1 : P * G2 ≤ P * ((D + 4) * L) := mul_le_mul_of_nonneg_left hG2 hP
  have h2 : P * G1 ≤ P * (2 * L) := mul_le_mul_of_nonneg_left hG1 hP
  have h3 : 0 ≤ P * L := mul_nonneg hP (by linarith)
  have h4 : P * L ≤ P * D * L := by nlinarith [mul_nonneg h3 (sub_nonneg.mpr hD)]
  have h5 : lNc ≤ lNc * L := by nlinarith [mul_nonneg hl (sub_nonneg.mpr hL)]
  constructor <;> nlinarith
end PI.UnitaryGroupMassFormula.TBNum
