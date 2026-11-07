-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_interior_dense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:46.109981+00:00
-- url     : https://prove2.me/submissions/77e0217f-8884-410b-bb13-2fa66792058e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.ClusterPt
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_nonzero_lift
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_target_open
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_target_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_param_continuous
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
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] :
    letI := lpsOriginalFilledTopology N
    DenseRange (Sum.inl : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) := by
  let := lpsOriginalFilledTopology N
  intro x
  cases x with
  | inl y => exact subset_closure ⟨y,rfl⟩
  | inr c =>
    rw [mem_closure_iff]
    intro U hU hc
    let r := lpsOriginalCuspRepresentative N c
    let e := lpsOriginalFilledCuspPartialEquiv N r
    let q0 : e.target := ⟨0,lpsOriginalFilledCuspPartialEquiv_target_zero N r⟩
    have hzero : lpsOriginalFilledCuspParam N c q0=Sum.inr c :=
      lpsOriginalFilledCuspParam_zero N c q0 rfl
    have hV : IsOpen (lpsOriginalFilledCuspParam N c ⁻¹' U) :=
      hU.preimage (lpsOriginalFilledTopology_param_continuous N c)
    have hW : IsOpen (Subtype.val '' (lpsOriginalFilledCuspParam N c ⁻¹' U)) :=
      (lpsOriginalFilledCuspPartialEquiv_target_open N r).isOpenMap_subtype_val _ hV
    have hn : (Subtype.val '' (lpsOriginalFilledCuspParam N c ⁻¹' U)).Nonempty :=
      ⟨0,q0,by change lpsOriginalFilledCuspParam N c q0∈U;rw [hzero];exact hc,rfl⟩
    obtain ⟨q,hq,hqw⟩ := (dense_compl_singleton (0:ℂ)).exists_mem_open hW hn
    obtain ⟨z,hz,he⟩ := hqw
    have hz0 : z.val≠0 := by simpa only [he,Set.mem_compl_iff,Set.mem_singleton_iff] using hq
    obtain ⟨τ,hτ,_⟩ := lpsOriginalFilledCuspParam_nonzero_lift N c z hz0
    refine ⟨lpsOriginalFilledCuspParam N c z,hz,?_⟩
    exact ⟨lpsOriginalCuspProjection N r τ,hτ.symm⟩
end QEC.Coding.TannerLiftedProduct
