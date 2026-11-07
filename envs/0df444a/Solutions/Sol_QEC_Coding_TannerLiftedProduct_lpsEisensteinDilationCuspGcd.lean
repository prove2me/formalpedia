-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEisensteinDilationCuspGcd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:19:28.179907+00:00
-- url     : https://prove2.me/submissions/a16d87e2-940c-42de-9f6d-6213c73b7518

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinDilationCuspMatrix_column

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N r : ℤ) (m : ℕ) (hm : 0<m) (γ : SL(2,ℤ)) :
    Int.gcd (N*(m:ℤ)*γ 0 0+r*γ 1 0) (N*γ 1 0)=
      Int.gcd (m:ℤ) (γ 1 0)*
        Int.gcd (N*lpsEisensteinDilationCuspMatrix m hm γ 0 0+
          r*lpsEisensteinDilationCuspMatrix m hm γ 1 0)
          (N*lpsEisensteinDilationCuspMatrix m hm γ 1 0) := by
  have h := lpsEisensteinDilationCuspMatrix_column m hm γ
  have heA : N*(m:ℤ)*γ 0 0+r*γ 1 0=(Int.gcd (m:ℤ) (γ 1 0):ℤ)*
      (N*lpsEisensteinDilationCuspMatrix m hm γ 0 0+
        r*lpsEisensteinDilationCuspMatrix m hm γ 1 0) := by
    linear_combination N*h.1+r*h.2
  have heC : N*γ 1 0=(Int.gcd (m:ℤ) (γ 1 0):ℤ)*
      (N*lpsEisensteinDilationCuspMatrix m hm γ 1 0) := by linear_combination N*h.2
  rw [heA,heC,Int.gcd_mul_left,Int.natAbs_natCast]
end QEC.Coding.TannerLiftedProduct
