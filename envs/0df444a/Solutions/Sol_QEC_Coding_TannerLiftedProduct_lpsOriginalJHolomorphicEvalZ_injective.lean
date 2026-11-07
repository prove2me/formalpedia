-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJHolomorphicEvalZ_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:32:48.688021+00:00
-- url     : https://prove2.me/submissions/571d8546-aa0f-4f8e-83f5-225aaae3893c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Integral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Function.Injective lpsOriginalJHolomorphicEvalZ :=
  lpsOriginalJHolomorphicEvalQ_injective.comp lpsOriginalIntegerCoefficientMap_injective
end QEC.Coding.TannerLiftedProduct
