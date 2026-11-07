-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicReduction_root_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:16.435882+00:00
-- url     : https://prove2.me/submissions/d6c93257-d03b-440b-a72d-b7deb1049b11

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicReduction_root

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] (m : ℕ) :
    lpsOriginalCyclotomicReduction p
      ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^m)=1 := by
  rw [map_pow,lpsOriginalCyclotomicReduction_root,one_pow]
end QEC.Coding.TannerLiftedProduct
