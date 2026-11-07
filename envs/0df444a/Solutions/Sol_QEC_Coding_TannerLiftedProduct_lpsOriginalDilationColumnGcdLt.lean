-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalDilationColumnGcdLt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:17:50.420362+00:00
-- url     : https://prove2.me/submissions/9c17abea-2f9a-42b2-a24b-b5e66b4abb19

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDilationColumnGcdDvd

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N)
    (γ : SL(2,ℤ)) (hc : ¬(N:ℤ)∣γ 1 0) :
    Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0)<N := by
  have hle := Nat.le_of_dvd hN (lpsOriginalDilationColumnGcdDvd N γ)
  apply lt_of_le_of_ne hle
  intro he
  have h := Int.gcd_dvd_right ((N:ℤ)*γ 0 0) (γ 1 0)
  rw [he] at h
  exact hc h
end QEC.Coding.TannerLiftedProduct
