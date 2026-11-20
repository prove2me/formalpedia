-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaIntegerDenominator_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:42:45.216185+00:00
-- url     : https://prove2.me/submissions/28539b04-6d22-498d-8b6f-c20384d41fb9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] :
    lpsThetaIntegerDenominator q≠0 := by
  have hq : 2≤(q : ℤ) := by exact_mod_cast (Fact.out : q.Prime).two_le
  unfold lpsThetaIntegerDenominator
  have hq2 : 0<(q : ℤ)^2-1 := by nlinarith
  positivity
end QEC.Coding.TannerLiftedProduct
