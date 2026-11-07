-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicComplexEmbedding_root_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:19.443136+00:00
-- url     : https://prove2.me/submissions/c6c270cc-e752-462b-92f2-a38081c39800

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicComplexEmbedding_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicRoot_inverse

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    lpsOriginalCyclotomicComplexEmbedding p ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^(p-1))=
      (lpsOriginalCyclotomicComplexRoot p)⁻¹ := by
  have h:=congrArg (lpsOriginalCyclotomicComplexEmbedding p) (lpsOriginalCyclotomicRoot_inverse p)
  rw [map_mul,map_one,lpsOriginalCyclotomicComplexEmbedding_root] at h
  exact eq_inv_of_mul_eq_one_right h
end QEC.Coding.TannerLiftedProduct
