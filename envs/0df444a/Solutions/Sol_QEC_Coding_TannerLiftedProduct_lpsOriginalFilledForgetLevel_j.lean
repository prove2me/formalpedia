-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_j
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:06:25.366385+00:00
-- url     : https://prove2.me/submissions/6c62f62b-5f13-4fb1-8f90-f93ad1b7f437

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) (hNM : N ∣ M) (x : LPSOriginalFilledCurve M) :
    lpsOriginalFilledJ N (lpsOriginalFilledForgetLevel N M hNM x) = lpsOriginalFilledJ M x := by
  cases x with
  | inl y => induction y using Quotient.inductionOn; rfl
  | inr c => rfl
end QEC.Coding.TannerLiftedProduct
