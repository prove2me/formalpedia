-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_Ji_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:25:32.678943+00:00
-- url     : https://prove2.me/submissions/1fbb0cb0-07ac-4f08-a6fa-4851f89e323f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn
import Theorems.Thm_Formalism_REAL_Jm_mul_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (a b : Matrix (Fin n) (Fin n) ℂ) : slmJi ε (a * b) = slmJi ε b * slmJi ε a := by
  unfold slmJi
  rw [Matrix.conjTranspose_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), Formalism.REAL.Jm_mul_self, one_mul]
end ReciprocityTheory.ChartRestriction.DS
