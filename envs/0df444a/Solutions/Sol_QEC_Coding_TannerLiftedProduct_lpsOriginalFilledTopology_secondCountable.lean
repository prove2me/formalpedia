-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_secondCountable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:03:23.649814+00:00
-- url     : https://prove2.me/submissions/06276c6f-a41f-4ba4-bd04-25043ee39675

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_param_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_param_open
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_open
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_target_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0Quotient_secondCountable


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] :
    @SecondCountableTopology (LPSOriginalFilledCurve N) (lpsOriginalFilledTopology N) := by
  let := lpsOriginalFilledTopology N
  let : SecondCountableTopology (MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :=
    lpsOriginalGamma0Quotient_secondCountable N
  let C := CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
  let D := MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ ⊕
      (Σ c : C, (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
  let f : D → LPSOriginalFilledCurve N :=
    Sum.elim Sum.inl (fun cq => lpsOriginalFilledCuspParam N cq.1 cq.2)
  have hc : Continuous f := continuous_sumElim.mpr
    ⟨lpsOriginalFilledTopology_interior_continuous N,
      continuous_sigma (fun c => lpsOriginalFilledTopology_param_continuous N c)⟩
  have ho : IsOpenMap f := isOpenMap_sumElim.mpr
    ⟨lpsOriginalFilledTopology_interior_open N,
      isOpenMap_sigma.mpr (fun c => lpsOriginalFilledTopology_param_open N c)⟩
  have hs : Function.Surjective f := by
    intro x
    cases x with
    | inl y => exact ⟨Sum.inl y,rfl⟩
    | inr c =>
      let q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target :=
        ⟨0,lpsOriginalFilledCuspPartialEquiv_target_zero N _⟩
      exact ⟨Sum.inr ⟨c,q⟩,lpsOriginalFilledCuspParam_zero N c q rfl⟩
  exact (ho.isQuotientMap hc hs).secondCountableTopology ho
end QEC.Coding.TannerLiftedProduct
