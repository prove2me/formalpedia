-- Prove2me | solution 1 for SpherePacking.isometricPackingKernel_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/d92ac3bb-717e-4dfe-911c-4eeab83f3b6f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_isometric_mixed_kernel_nonneg

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
    (x y : Euclidean n) :
    0 ≤ isometricPackingKernel f x y := by
  exact isometric_mixed_kernel_nonneg
    (certificateAmbientBasis n k L)
    (certificateFibreBasis n k) f x y
end SpherePacking
