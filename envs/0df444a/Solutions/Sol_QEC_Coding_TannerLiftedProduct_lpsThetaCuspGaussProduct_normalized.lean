-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:04:22.419484+00:00
-- url     : https://prove2.me/submissions/de7defec-cabf-4675-baab-c7bb85c87899

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_all_factors

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q N : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (hN : 0<N) (γ : SL(2,ℤ)) (hC : γ 1 0=(N:ℤ)) :
    -(32*(q:ℂ)^3*(N:ℂ)^2)⁻¹*lpsThetaCuspGaussProduct q (γ 0 0) N=
      -lpsThetaEisensteinNormalization q*
        (lpsThetaEisensteinTwoCuspFactor γ+lpsChi4EisensteinCuspConstant γ)*
        (lpsThetaEisensteinPrimeCuspFactor q γ+lpsQuadraticEisensteinCuspConstant q γ) := by
  have hq : (q:ℂ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hn : (N:ℂ)≠0 := by exact_mod_cast hN.ne'
  have hqs : (q:ℂ)^2-1≠0 := by
    have hr : (1:ℝ)<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
    have hs : (q:ℝ)^2-1≠0 := by nlinarith
    exact_mod_cast hs
  rw [lpsThetaCuspGaussProduct_all_factors q N hq4 hN γ hC]
  unfold lpsThetaEisensteinNormalization
  field_simp [hq,hn,hqs]
  ring
end QEC.Coding.TannerLiftedProduct
