-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEisensteinDilationCuspMatrix_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:03:34.92747+00:00
-- url     : https://prove2.me/submissions/9128aca1-acfc-47e8-8eaa-588424cbe6bd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ) (hm : 0<m) (γ : SL(2,ℤ)) :
    (m:ℤ)*γ 0 0=(Int.gcd (m:ℤ) (γ 1 0):ℤ)*lpsEisensteinDilationCuspMatrix m hm γ 0 0 ∧
      γ 1 0=(Int.gcd (m:ℤ) (γ 1 0):ℤ)*lpsEisensteinDilationCuspMatrix m hm γ 1 0 := by
  have hA := Int.mul_ediv_cancel_of_dvd (Int.gcd_dvd_left ((m:ℤ)*γ 0 0) (γ 1 0))
  have hC := Int.mul_ediv_cancel_of_dvd (Int.gcd_dvd_right ((m:ℤ)*γ 0 0) (γ 1 0))
  constructor
  · change (m:ℤ)*γ 0 0=(Int.gcd (m:ℤ) (γ 1 0):ℤ)*
      (((m:ℤ)*γ 0 0)/(Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0):ℤ))
    rw [lpsEisensteinDilation_column_gcd] at hA ⊢
    exact hA.symm
  · change γ 1 0=(Int.gcd (m:ℤ) (γ 1 0):ℤ)*
      ((γ 1 0)/(Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0):ℤ))
    rw [lpsEisensteinDilation_column_gcd] at hC ⊢
    exact hC.symm
end QEC.Coding.TannerLiftedProduct
