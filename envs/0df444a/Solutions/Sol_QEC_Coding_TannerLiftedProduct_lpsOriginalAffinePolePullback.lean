-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAffinePolePullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:21:18.628821+00:00
-- url     : https://prove2.me/submissions/b3209e83-e4da-4a21-86d0-c3b44b381a27

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffineNome
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_qParam_pullback


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m k : ℕ) (hm : 0<m)
    (hmk : m≤k) (r : ℝ) (τ : ℍ) :
    Function.Periodic.qParam 1 (τ:ℂ)^k*
      lpsOriginalJInvariant (lpsE2AffineMatrix m hm r • τ)=
        Function.Periodic.qParam 1 (τ:ℂ)^(k-m)/Function.Periodic.qParam 1 (r:ℂ)*
          lpsOriginalJQCoefficient
            (Function.Periodic.qParam 1 ((lpsE2AffineMatrix m hm r • τ:ℍ):ℂ)) := by
  have h := lpsOriginalJInvariant_qParam_pullback (lpsE2AffineMatrix m hm r • τ)
  rw [lpsOriginalAffineNome] at h
  have he : Function.Periodic.qParam 1 (τ:ℂ)^k=
      Function.Periodic.qParam 1 (τ:ℂ)^(k-m)*Function.Periodic.qParam 1 (τ:ℂ)^m := by
    rw [←pow_add,Nat.sub_add_cancel hmk]
  rw [he,lpsOriginalAffineNome,←h]
  field_simp [Function.Periodic.qParam_ne_zero]
end QEC.Coding.TannerLiftedProduct
