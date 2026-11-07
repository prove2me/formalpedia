-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCusp_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:52:53.471273+00:00
-- url     : https://prove2.me/submissions/243502d0-666e-438e-8d48-db43df168e95

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Character_ne_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (A D : ZMod q) (hD : D≠0) :
    (∑ r : ZMod q,lpsQuadraticE2Character q r*(if A+r*D=0 then (q:ℂ)^2 else 1))=
      ((q:ℂ)^2-1)*lpsQuadraticE2Character q (-A/D) := by
  classical
  have hc : (∑ r : ZMod q,lpsQuadraticE2Character q r)=0 :=
    MulChar.sum_eq_zero_of_ne_one (lpsQuadraticE2Character_ne_one q hq2)
  have he (r : ZMod q) : A+r*D=0 ↔ r= -A/D := by
    constructor
    · intro h
      apply (eq_div_iff hD).mpr
      linear_combination h
    · intro h
      have hh := (eq_div_iff hD).mp h
      linear_combination hh
  simp_rw [he]
  have hs : (∑ r : ZMod q,lpsQuadraticE2Character q r*(if r= -A/D then (q:ℂ)^2 else 1))=
      (∑ r : ZMod q,lpsQuadraticE2Character q r)+
        ((q:ℂ)^2-1)*(∑ r : ZMod q,if r= -A/D then lpsQuadraticE2Character q r else 0) := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    split_ifs <;> ring
  rw [hs,hc]
  simp
end QEC.Coding.TannerLiftedProduct
