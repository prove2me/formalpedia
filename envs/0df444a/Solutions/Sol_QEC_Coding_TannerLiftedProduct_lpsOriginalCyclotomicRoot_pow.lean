-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicRoot_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:13.452208+00:00
-- url     : https://prove2.me/submissions/814fc03d-4d62-4238-82e3-04cc5e630374

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicComplexEmbedding_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicComplexEmbedding_root

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    (AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^p=1 := by
  apply lpsOriginalCyclotomicComplexEmbedding_injective p
  rw [map_pow,map_one,lpsOriginalCyclotomicComplexEmbedding_root]
  exact (lpsOriginalCyclotomicComplexRoot_primitive p).pow_eq_one
end QEC.Coding.TannerLiftedProduct
