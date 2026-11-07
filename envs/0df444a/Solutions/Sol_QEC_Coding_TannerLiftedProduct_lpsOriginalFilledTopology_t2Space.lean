-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_t2Space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:56:52.213276+00:00
-- url     : https://prove2.me/submissions/de3300ad-3f4e-47fc-b9c5-efdadf9eb3df

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_param_openEmbedding
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_open
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_cusp_separation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspRepresentative_orbit
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_range
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_sources_disjoint
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_target_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0Quotient_t2
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] :
    @T2Space (LPSOriginalFilledCurve N) (lpsOriginalFilledTopology N) := by
  let := lpsOriginalFilledTopology N
  let : T2Space (MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) := lpsOriginalGamma0Quotient_t2 N
  constructor
  intro x y hxy
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      have hab : a≠b := fun h => hxy (congrArg Sum.inl h)
      obtain ⟨u,v,hu,hv,ha,hb,hd⟩ := t2_separation hab
      refine ⟨Sum.inl '' u,Sum.inl '' v,lpsOriginalFilledTopology_interior_open N u hu,
        lpsOriginalFilledTopology_interior_open N v hv,⟨a,ha,rfl⟩,⟨b,hb,rfl⟩,?_⟩
      apply Set.disjoint_left.mpr
      rintro z ⟨a',ha',rfl⟩ ⟨b',hb',he⟩
      have he' := Sum.inl.inj he
      subst b'
      exact Set.disjoint_left.mp hd ha' hb'
    | inr c => exact lpsOriginalFilledTopology_interior_cusp_separation N a c
  | inr c =>
    cases y with
    | inl a =>
      obtain ⟨u,v,hu,hv,ha,hc,hd⟩ := lpsOriginalFilledTopology_interior_cusp_separation N a c
      exact ⟨v,u,hv,hu,hc,ha,hd.symm⟩
    | inr d =>
      have hcd : c≠d := fun h => hxy (congrArg Sum.inr h)
      have hc := lpsOriginalFilledTopology_param_openEmbedding N c
      have hd := lpsOriginalFilledTopology_param_openEmbedding N d
      refine ⟨Set.range (lpsOriginalFilledCuspParam N c),Set.range (lpsOriginalFilledCuspParam N d),
        hc.isOpen_range,hd.isOpen_range,?_,?_,?_⟩
      · let q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target :=
          ⟨0,lpsOriginalFilledCuspPartialEquiv_target_zero N _⟩
        exact ⟨q,lpsOriginalFilledCuspParam_zero N c q rfl⟩
      · let q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N d)).target :=
          ⟨0,lpsOriginalFilledCuspPartialEquiv_target_zero N _⟩
        exact ⟨q,lpsOriginalFilledCuspParam_zero N d q rfl⟩
      · rw [lpsOriginalFilledCuspParam_range,lpsOriginalFilledCuspParam_range]
        exact lpsOriginalFilledCuspPartialEquiv_sources_disjoint N _ _ (by
          simpa only [lpsOriginalCuspRepresentative_orbit] using hcd)
end QEC.Coding.TannerLiftedProduct
