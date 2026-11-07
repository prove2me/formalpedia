-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2PrimeCusp_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:01:22.260787+00:00
-- url     : https://prove2.me/submissions/6f9ac09e-07d7-4902-95ff-21036a87ad00

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
      (if r.val+1=q then (q:ℂ)^2 else 1)) =
        lpsQuadraticE2Character q (-1:ZMod q)*((q:ℂ)^2-1) := by
  classical
  have hq : 0<q := (Fact.out : q.Prime).pos
  let last : Fin q := ⟨q-1,Nat.sub_lt hq (by decide)⟩
  have hl : last.val+1=q := by dsimp [last];omega
  have hc : (last.val:ZMod q)= -1 := by
    have h : (last.val:ZMod q)+1=0 := by
      simpa only [Nat.cast_add,Nat.cast_one,ZMod.natCast_self] using
        congrArg (fun n : ℕ => (n:ZMod q)) hl
    linear_combination h
  have hr (r : Fin q) : r.val+1=q ↔ r=last := by
    constructor
    · intro h;apply Fin.ext;omega
    · intro h;subst r;exact hl
  simp_rw [hr]
  have he (r : Fin q) : lpsQuadraticE2Character q (r.val:ZMod q)*
      (if r=last then (q:ℂ)^2 else 1) =
      lpsQuadraticE2Character q (r.val:ZMod q)+
        (if r=last then lpsQuadraticE2Character q (last.val:ZMod q)*((q:ℂ)^2-1) else 0) := by
    by_cases h : r=last
    · subst r;simp;ring
    · simp only [if_neg h,mul_one,add_zero]
  simp_rw [he]
  rw [Finset.sum_add_distrib,lpsQuadraticE2Character_sum_zero q hq2]
  simp [hc]
end QEC.Coding.TannerLiftedProduct
