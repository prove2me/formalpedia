-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedMeromorphicCovector_class
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:00:59.267753+00:00
-- url     : https://prove2.me/submissions/fdaca8f2-12b0-4834-a080-674c7b5968c6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeHolomorphicExtension
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledCovector_codiscrete
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (sigma : LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) :
    lpsOriginalCompactMeromorphicCovectorClass N hN sigma =
      lpsOriginalCompactMeromorphicCovectorClass N hN
        (lpsOriginalNormalizedMeromorphicCovectorRepresentative N hN sigma) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let : AddCommGroup (LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) :=
    (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
  change Submodule.Quotient.mk sigma =
    Submodule.Quotient.mk (lpsOriginalNormalizedMeromorphicCovectorRepresentative N hN sigma)
  apply (Submodule.Quotient.eq (lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN)).mpr
  change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N),
    sigma.val y - lpsOriginalNormalizedFilledCovector N hN sigma.val y = 0
  filter_upwards [lpsOriginalNormalizedFilledCovector_codiscrete N hN sigma.val sigma.property]
    with y hy
  exact sub_eq_zero.mpr hy
end QEC.Coding.TannerLiftedProduct
