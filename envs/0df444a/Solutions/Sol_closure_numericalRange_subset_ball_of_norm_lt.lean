-- Prove2me | solution 1 for closure_numericalRange_subset_ball_of_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:00:35.336448+00:00
-- url     : https://prove2.me/submissions/a844d4c6-92bb-4608-88a0-a5a36a23affa

import Definitions.Def_Operator_Crouzeix_CircleKernel
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleProduct
import Definitions.Def_Operator_Crouzeix_Palencia
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Theorems.Thm_norm_le_of_mem_numericalRange


set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) :
    closure (numericalRange A) ⊆ Metric.ball (0 : ℂ) R := by
  have h1 : numericalRange A ⊆ Metric.closedBall (0 : ℂ) ‖A‖ := fun z hz => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_of_mem_numericalRange A hz
  exact (closure_minimal h1 Metric.isClosed_closedBall).trans
    (Metric.closedBall_subset_ball hR)
