-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicRoot_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:58.964235+00:00
-- url     : https://prove2.me/submissions/037e31d7-635f-431d-83bc-6e345d587fb5

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicRoot_pow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    AdjoinRoot.root (Polynomial.cyclotomic p ℤ)*
      (AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^(p-1)=1 := by
  rw [←pow_succ',Nat.sub_add_cancel (Fact.out : p.Prime).one_le,
    lpsOriginalCyclotomicRoot_pow]
end QEC.Coding.TannerLiftedProduct
