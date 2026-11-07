-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToSpecZ_locallyOfFinitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:14:56.769603+00:00
-- url     : https://prove2.me/submissions/bf1a4122-f2e7-4627-b955-d94378e23396

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToSpecZ_proper


set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    LocallyOfFinitePresentation (lpsOriginalIntegerNormalGluedToSpecZ N hN) := by
  let := lpsOriginalIntegerNormalGluedToSpecZ_proper N hN
  infer_instance
end QEC.Coding.TannerLiftedProduct
