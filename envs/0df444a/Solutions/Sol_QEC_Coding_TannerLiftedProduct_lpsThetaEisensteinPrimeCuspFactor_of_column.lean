-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinPrimeCuspFactor_of_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:50:51.973174+00:00
-- url     : https://prove2.me/submissions/eee197fb-c5f3-4bba-b090-ad818f8f1097

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimePowerCuspGcd

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q v L : ℕ) [Fact q.Prime]
    (hc : q.Coprime L) (γ : SL(2,ℤ)) (hC : γ 1 0=((q^v*L:ℕ):ℤ)) :
    lpsThetaEisensteinPrimeCuspFactor q γ=
      if v=0 then ((q:ℂ)^2-1)/(q:ℂ)^2 else if v=1 then 0 else (q:ℂ)*((q:ℂ)^2-1) := by
  unfold lpsThetaEisensteinPrimeCuspFactor
  simp_rw [hC,lpsPrimePowerCuspGcd q _ v L hc]
  have hq : (q:ℂ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  by_cases h0 : v=0
  · subst v
    norm_num [lpsThetaEisensteinPrimeWeight,Fin.sum_univ_succ]
    field_simp [hq]
    ring
  · rw [if_neg h0]
    by_cases h1 : v=1
    · subst v
      norm_num [lpsThetaEisensteinPrimeWeight,Fin.sum_univ_succ]
      field_simp [hq]
      ring
    · rw [if_neg h1]
      have hv : 2≤v := by omega
      have hm (b : Fin 3) : min b.val v=b.val := min_eq_left (by omega)
      simp_rw [hm]
      norm_num [lpsThetaEisensteinPrimeWeight,Fin.sum_univ_succ]
      field_simp [hq]
      ring
end QEC.Coding.TannerLiftedProduct
