-- Prove2me | solution 1 for closure_numericalRange_subset_closedBall_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:17:40.592059+00:00
-- url     : https://prove2.me/submissions/225be1ea-74dc-4072-9a92-f778b472e53e

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_norm_le_numericalRadius


set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) :
    closure (numericalRange A) ⊆ Metric.closedBall 0 (numericalRadius A) := by
  apply closure_minimal
  · intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_numericalRadius A hz
  · exact Metric.isClosed_closedBall
