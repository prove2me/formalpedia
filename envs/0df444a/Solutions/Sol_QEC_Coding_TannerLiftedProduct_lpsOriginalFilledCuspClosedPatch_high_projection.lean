-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspClosedPatch_high_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:48:46.067508+00:00
-- url     : https://prove2.me/submissions/6b071869-92ac-487e-bfe7-31c43c112a1f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspNeighborhood_change_point
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspRepresentative_orbit


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (ρ : SL(2,ℤ)) (σ : {τ : ℍ // 1<τ.im}) (hs : 2≤σ.val.im) :
    Sum.inl (lpsOriginalCuspProjection N ρ σ)∈
      lpsOriginalFilledCuspClosedPatch N (lpsOriginalCuspOrbit N ρ) := by
  let c := lpsOriginalCuspOrbit N ρ
  let r := lpsOriginalCuspRepresentative N c
  obtain ⟨τ,ht,he⟩ := lpsOriginalCuspNeighborhood_change_point N r ρ
    (lpsOriginalCuspRepresentative_orbit N c) σ
  let w := (lpsOriginalCuspGroup N r).strictWidthInfty
  let q := Function.Periodic.qParam w τ.val
  have hw : 0<w := lpsOriginalCuspGroup_width_positive N r
  have hq : q∈Metric.closedBall (0:ℂ) (Real.exp (-2*Real.pi*2/w)) := by
    rw [mem_closedBall_zero_iff]
    change ‖Function.Periodic.qParam w τ.val‖≤_
    rw [Function.Periodic.norm_qParam,UpperHalfPlane.coe_im,ht]
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff_of_pos_right hw).mpr
    nlinarith [Real.pi_pos]
  refine ⟨q,hq,?_⟩
  have hp : Sum.inl (lpsOriginalCuspProjection N r τ)∈
      (lpsOriginalFilledCuspPartialEquiv N r).source := ⟨τ,rfl⟩
  have hi := (lpsOriginalFilledCuspPartialEquiv N r).left_inv hp
  rw [lpsOriginalFilledCuspPartialEquiv_projection,he] at hi
  exact hi
end QEC.Coding.TannerLiftedProduct
