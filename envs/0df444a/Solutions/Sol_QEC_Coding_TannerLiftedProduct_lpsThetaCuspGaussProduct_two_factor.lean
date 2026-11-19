-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_two_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:53:00.998642+00:00
-- url     : https://prove2.me/submissions/8c0c0ce5-0584-461f-abb9-e4b6a0d3bd6e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisensteinTwoCuspFactor_of_column
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4EisensteinCuspConstant_of_column
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_eight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_four_character
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_two
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_two_pow_ge_four


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q t L : ℕ) (hq : Odd q) (hL : Odd L)
    (γ : SL(2,ℤ)) (hC : γ 1 0=((2^t*L:ℕ):ℤ))
    (ha : IsUnit ((γ 0 0 * (L : ℤ) : ℤ) : ZMod (2 ^ t))) :
    lpsThetaCuspGaussProduct q (γ 0 0*(L:ℤ)) (2^t)=
      (4/3:ℂ)*((2^t:ℕ):ℂ)^2*
        (lpsThetaEisensteinTwoCuspFactor γ+lpsChi4EisensteinCuspConstant γ) := by
  rw [lpsThetaEisensteinTwoCuspFactor_of_column t L hL γ hC,
    lpsChi4EisensteinCuspConstant_of_column t L hL γ hC]
  by_cases h0 : t=0
  · subst t
    rw [pow_zero,lpsThetaCuspGaussProduct_one]
    norm_num
  · rw [if_neg h0]
    by_cases h1 : t=1
    · subst t
      norm_num only [Nat.reducePow] at ha ⊢
      rw [lpsThetaCuspGaussProduct_two q _ ha]
      norm_num
    · rw [if_neg h1]
      by_cases h2 : t=2
      · subst t
        norm_num only [Nat.reducePow] at ha ⊢
        rw [lpsThetaCuspGaussProduct_four_character q _ ha]
        norm_num
        ring
      · rw [if_neg h2,if_neg h2]
        by_cases h3 : t=3
        · subst t
          norm_num only [Nat.reducePow] at ha ⊢
          rw [lpsThetaCuspGaussProduct_eight q hq _ ha]
          norm_num
        · rw [if_neg h3]
          have ht : 4≤t := by omega
          obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le ht
          have he' : t=e+4 := by omega
          rw [he'] at ha ⊢
          rw [lpsThetaCuspGaussProduct_two_pow_ge_four q hq e _ ha]
          ring
end QEC.Coding.TannerLiftedProduct
