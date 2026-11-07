-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_uniform_cusp_pole_clearing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:32:14.90456+00:00
-- url     : https://prove2.me/submissions/693a14ed-2ba1-4ea5-8ef9-a49640c2f5dc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction
import Mathlib.Analysis.Analytic.Polynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspChart_cusp
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    letI := lpsOriginalFilledTopology N
    ∃ k : ℕ, ∀ c : CuspOrbits
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
      AnalyticAt ℂ (fun q : ℂ => q^k *
        F ((lpsOriginalFilledCuspChart N c).symm q)) 0 := by
  classical
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let C := CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
  let := Fintype.ofFinite C
  have hc (c : C) : ∃ n : ℕ, AnalyticAt ℂ
      (fun q : ℂ => q^n * F ((lpsOriginalFilledCuspChart N c).symm q)) 0 := by
    have hz : (0 : ℂ) ∈ (lpsOriginalFilledCuspChart N c).target := by
      rw [← lpsOriginalFilledCuspChart_cusp N c]
      exact (lpsOriginalFilledCuspChart N c).map_source
        (lpsOriginalFilledCuspChart_mem_cusp N c)
    have h := hF (Sum.inr c) 0 hz
    obtain ⟨n,hn⟩ := h
    refine ⟨n,?_⟩
    have hchart : chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) =
        lpsOriginalFilledCuspChart N c := rfl
    simp only [sub_zero,smul_eq_mul,hchart,Function.comp_apply] at hn
    convert! hn using 1
  let n : C → ℕ := fun c => (hc c).choose
  let k := ∑ c : C, n c
  refine ⟨k,?_⟩
  intro c
  have hnk : n c ≤ k := Finset.single_le_sum (fun d hd => Nat.zero_le (n d))
    (Finset.mem_univ c)
  have ha := (hc c).choose_spec
  have hh := (analyticAt_id.pow (k-n c)).mul ha
  convert! hh using 1
  funext q
  simp only [Pi.mul_apply,Pi.pow_apply,id_eq]
  rw [←mul_assoc,←pow_add,Nat.sub_add_cancel hnk]
end QEC.Coding.TannerLiftedProduct
