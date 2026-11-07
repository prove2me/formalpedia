-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinCorrectionCoefficient_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:34:36.218335+00:00
-- url     : https://prove2.me/submissions/733ebb3d-9e11-4658-acba-cca8cdb01e24

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2DifferenceCoefficient_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] :
    lpsThetaEisensteinCorrectionCoefficient q 0=1 := by
  have hqC : (q:ℂ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hq2C : (q:ℂ)^2-1≠0 := by
    have hr : (1:ℝ)<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
    have hx : (q:ℝ)^2-1≠0 := by nlinarith
    exact_mod_cast hx
  norm_num [lpsThetaEisensteinCorrectionCoefficient,lpsThetaEisensteinNormalization,
    lpsE2DifferenceCoefficient_zero,lpsThetaEisensteinTwoWeight,lpsThetaEisensteinPrimeWeight,
    lpsThetaEisensteinChi4Weight,lpsThetaEisensteinQuadraticWeight,Fin.sum_univ_succ,
    MulChar.map_zero,Nat.cast_mul,Nat.cast_pow]
  field_simp [hqC,hq2C]
  ring
end QEC.Coding.TannerLiftedProduct
