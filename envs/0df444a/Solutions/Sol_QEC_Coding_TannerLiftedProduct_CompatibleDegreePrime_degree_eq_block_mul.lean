-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.CompatibleDegreePrime.degree_eq_block_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:26:40.708788+00:00
-- url     : https://prove2.me/submissions/8a87e5fb-8f0e-4b2c-92a5-ae55302d99a5

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
namespace CompatibleDegreePrime
theorem _root_.solution
    {A : Nat} (a : CompatibleDegreePrime A) :
    a.p + 1 = A * a.blocks := by
  symm
  exact Nat.mul_div_cancel' a.blockDvdDegree
end CompatibleDegreePrime
end QEC.Coding.TannerLiftedProduct
