-- Prove2me | solution 1 for closure_numericalRange_subset_closedBall_centered_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:24:02.531808+00:00
-- url     : https://prove2.me/submissions/fcb39704-305b-4d45-acef-c41bbb1571ec

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_norm_le_numericalRadius
import Theorems.Thm_numericalRange_sub_smul_one


set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) :
    closure (numericalRange A) ⊆
      Metric.closedBall c (numericalRadius (A - c • 1)) := by
  apply closure_minimal
  · intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    apply norm_le_numericalRadius (A - c • 1)
    rw [numericalRange_sub_smul_one]
    exact ⟨z, hz, rfl⟩
  · exact Metric.isClosed_closedBall
