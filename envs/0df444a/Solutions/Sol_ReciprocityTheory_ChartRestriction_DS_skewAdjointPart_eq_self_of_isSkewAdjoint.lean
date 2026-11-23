-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.skewAdjointPart_eq_self_of_isSkewAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:06.750072+00:00
-- url     : https://prove2.me/submissions/d15f9d11-bb15-41bc-8241-2b63803a181c

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_JJ

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
theorem _root_.solution {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Formalism.REAL.inG ε Y) : slmP ε Y = Y := by
  unfold Formalism.REAL.inG at hY
  have h1 : Yᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * Y) := eq_neg_of_add_eq_zero_left hY
  have h2 : Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε = -Y := by
    calc Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (Yᴴ * Formalism.REAL.Jm ε) := Matrix.mul_assoc _ _ _
      _ = -(Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Y)) := by rw [h1, Matrix.mul_neg]
      _ = -Y := by rw [slm_JJ]
  unfold slmP
  rw [h2, sub_neg_eq_add, ← two_smul ℂ Y, smul_smul]
  norm_num
end ReciprocityTheory.ChartRestriction.DS
