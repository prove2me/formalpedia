-- Prove2me | solution 1 for SpherePacking.isometricPackingKernel_trace_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/056a45e9-c628-4395-bbc7-fdb9098287aa

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_isometric_mixed_gram_trace_cauchy

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open SpherePacking
noncomputable section
set_option autoImplicit false
open Filter
open scoped BigOperators InnerProductSpace
namespace SpherePacking
theorem _root_.solution
    {n k L : ℕ}
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (C : Finset (Euclidean n)) :
    ((C.card : ℝ) * (Gegenbauer.fibreDimension n k : ℝ)) ^ 2 ≤
      (truncatedHarmonicDimension n k L : ℝ) *
        ∑ x ∈ C, ∑ y ∈ C, isometricPackingKernel f x y := by
  simpa [isometricPackingKernel, finrank_euclideanSpace_fin] using
    isometric_mixed_gram_trace_cauchy
      (certificateAmbientBasis n k L) C f
end SpherePacking
