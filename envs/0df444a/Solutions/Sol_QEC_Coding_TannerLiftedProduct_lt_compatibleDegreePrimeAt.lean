-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lt_compatibleDegreePrimeAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:51.765895+00:00
-- url     : https://prove2.me/submissions/9e14d99e-35d9-46d2-a954-1869c37c0903

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (A B : Nat) (hA : 0 < A) (hOdd : Odd A) :
    B < (compatibleDegreePrimeAt A B hA hOdd).p :=
  Classical.choose_spec (exists_compatibleDegreePrime_gt A B hA hOdd)
end QEC.Coding.TannerLiftedProduct
