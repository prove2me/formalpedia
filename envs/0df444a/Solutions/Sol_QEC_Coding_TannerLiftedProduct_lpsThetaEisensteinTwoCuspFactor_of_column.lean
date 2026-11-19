-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinTwoCuspFactor_of_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:50:24.150688+00:00
-- url     : https://prove2.me/submissions/887361b7-bbd6-40dc-8819-39ae798a6061

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimePowerCuspGcd

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (t L : ℕ) (hL : Odd L)
    (γ : SL(2,ℤ)) (hC : γ 1 0=((2^t*L:ℕ):ℤ)) :
    lpsThetaEisensteinTwoCuspFactor γ=
      if t=0 then 3/4 else if t=1 then 0 else if t=2 then 6 else if t=3 then 0 else -24 := by
  unfold lpsThetaEisensteinTwoCuspFactor
  simp_rw [hC,lpsPrimePowerCuspGcd 2 _ t L hL.coprime_two_left]
  by_cases h0 : t=0
  · subst t
    norm_num [lpsThetaEisensteinTwoWeight,Fin.sum_univ_succ]
  · rw [if_neg h0]
    by_cases h1 : t=1
    · subst t
      norm_num [lpsThetaEisensteinTwoWeight,Fin.sum_univ_succ]
    · rw [if_neg h1]
      by_cases h2 : t=2
      · subst t
        norm_num [lpsThetaEisensteinTwoWeight,Fin.sum_univ_succ]
      · rw [if_neg h2]
        by_cases h3 : t=3
        · subst t
          norm_num [lpsThetaEisensteinTwoWeight,Fin.sum_univ_succ]
        · rw [if_neg h3]
          have ht : 4≤t := by omega
          have hm (a : Fin 5) : min a.val t=a.val := min_eq_left (by omega)
          simp_rw [hm]
          norm_num [lpsThetaEisensteinTwoWeight,Fin.sum_univ_succ]
end QEC.Coding.TannerLiftedProduct
