-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_interior_cusp_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:52:03.285209+00:00
-- url     : https://prove2.me/submissions/5aaddc1a-ca81-445e-a12b-2428867fdd7b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_param_open
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_open
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_nonzero_lift
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_target_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0_projected_im_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0_quotientProjection_open
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
theorem _root_.solution (N : ℕ) [NeZero N]
    (y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    ∃ u v : Set (LPSOriginalFilledCurve N),
      IsOpen[lpsOriginalFilledTopology N] u ∧ IsOpen[lpsOriginalFilledTopology N] v ∧
        Sum.inl y∈u ∧ Sum.inr c∈v ∧ Disjoint u v := by
  let := lpsOriginalFilledTopology N
  obtain ⟨τ,rfl⟩ := Quotient.exists_rep y
  let A : Set ℍ := {σ | τ.im/2<σ.im ∧ σ.im<τ.im+1}
  let Y : ℝ := τ.im+1+2/τ.im+2
  let r := lpsOriginalCuspRepresentative N c
  let w := (lpsOriginalCuspGroup N r).strictWidthInfty
  let B : Set ((lpsOriginalFilledCuspPartialEquiv N r).target) :=
    {q | ‖q.val‖<Real.exp (-2*Real.pi*Y/w)}
  let π : ℍ → MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ :=
      Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
  have hA : IsOpen A := (isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
    (isOpen_lt UpperHalfPlane.continuous_im continuous_const)
  have hB : IsOpen B := isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  refine ⟨Sum.inl '' (π '' A),lpsOriginalFilledCuspParam N c '' B,
    lpsOriginalFilledTopology_interior_open N _ (lpsOriginalGamma0_quotientProjection_open N _ hA),
    lpsOriginalFilledTopology_param_open N c _ hB,?_,?_,?_⟩
  · refine ⟨⟦τ⟧,⟨τ,?_,rfl⟩,rfl⟩
    change τ.im/2<τ.im ∧ τ.im<τ.im+1
    constructor <;> linarith [τ.im_pos]
  · let q : (lpsOriginalFilledCuspPartialEquiv N r).target :=
      ⟨0,lpsOriginalFilledCuspPartialEquiv_target_zero N r⟩
    refine ⟨q,?_,lpsOriginalFilledCuspParam_zero N c q rfl⟩
    change ‖(0:ℂ)‖<_
    simpa only [norm_zero] using Real.exp_pos (-2*Real.pi*Y/w)
  · apply Set.disjoint_left.mpr
    rintro x ⟨a,⟨σ,hσ,heσ⟩,hex⟩ ⟨q,hq,heq⟩
    have hx : lpsOriginalFilledCuspParam N c q=Sum.inl (π σ) := by
      rw [heσ,hex]
      exact heq
    by_cases hz : q.val=0
    · rw [lpsOriginalFilledCuspParam_zero N c q hz] at hx
      cases hx
    obtain ⟨σ',heq',hq'⟩ := lpsOriginalFilledCuspParam_nonzero_lift N c q hz
    have hp : lpsOriginalGamma0Projected N r σ'.val=π σ :=
      Sum.inl.inj (heq'.symm.trans hx)
    have hb := lpsOriginalGamma0_projected_im_bound N r σ'.val σ hp
    have hw : 0<w := lpsOriginalCuspGroup_width_positive N r
    have hhigh : Y<σ'.val.im := by
      have hn : ‖Function.Periodic.qParam w σ'.val‖<Real.exp (-2*Real.pi*Y/w) := by
        rw [←hq']
        exact hq
      simpa only [UpperHalfPlane.coe_im] using
        (Function.Periodic.norm_qParam_lt_iff hw Y (σ'.val:ℂ)).mp hn
    change τ.im/2<σ.im ∧ σ.im<τ.im+1 at hσ
    have hi : 1/σ.im<2/τ.im := by
      apply (div_lt_div_iff₀ σ.im_pos τ.im_pos).mpr
      nlinarith [hσ.1]
    have hYb : τ.im+1<Y := by
      dsimp [Y]
      have hd : 0<2/τ.im := div_pos (by norm_num) τ.im_pos
      linarith
    have hYi : 2/τ.im<Y := by dsimp [Y];linarith [τ.im_pos]
    have hmax : max σ.im (1/σ.im)<Y := max_lt (hσ.2.trans hYb) (hi.trans hYi)
    linarith
end QEC.Coding.TannerLiftedProduct
