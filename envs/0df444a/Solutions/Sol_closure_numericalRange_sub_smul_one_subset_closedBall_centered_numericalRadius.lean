-- Prove2me | solution 1 for closure_numericalRange_sub_smul_one_subset_closedBall_centered_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:30:40.76062+00:00
-- url     : https://prove2.me/submissions/91fa00b0-a519-4a38-9eb5-be1e7c0c45ba

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_closure_numericalRange_subset_closedBall_numericalRadius

set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) :
    closure (numericalRange (A - c • (1 : E →L[ℂ] E))) ⊆
      Metric.closedBall 0
        (numericalRadius (A - c • (1 : E →L[ℂ] E))) :=
  closure_numericalRange_subset_closedBall_numericalRadius
    (A - c • (1 : E →L[ℂ] E))
