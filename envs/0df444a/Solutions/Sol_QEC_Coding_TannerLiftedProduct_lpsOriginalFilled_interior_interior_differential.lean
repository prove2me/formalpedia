-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_interior_interior_differential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:50:10.280882+00:00
-- url     : https://prove2.me/submissions/78d48ca4-452d-4108-80b8-ce41d126d5ff

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_localInverse_differential_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_symm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_target_pos
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_openEmbedding
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledInteriorChart N hN x).symm.trans
        (lpsOriginalFilledInteriorChart N hN y)).source) :
    letI := lpsOriginalFilledTopology N
    let e := (lpsOriginalFilledInteriorChart N hN x).symm.trans
      (lpsOriginalFilledInteriorChart N hN y)
    f (UpperHalfPlane.ofComplex (e z)) * deriv e z = f (UpperHalfPlane.ofComplex z) := by
  let := lpsOriginalFilledTopology N
  let := lpsGamma0QuotientChartedSpace N hN
  let proj := Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  have hp : Function.Surjective proj := Quotient.mk_surjective
  let r := hp.hasRightInverse.choose
  change z∈(lpsOriginalFilledInteriorChart N hN x).target ∧
    (lpsOriginalFilledInteriorChart N hN x).symm z∈
      (lpsOriginalFilledInteriorChart N hN y).source at hz
  have hpos := lpsOriginalFilledInteriorChart_target_pos N hN x z hz.1
  let τ : ℍ := ⟨z,hpos⟩
  have hm := hz.2
  rw [lpsOriginalFilledInteriorChart_symm,
    UpperHalfPlane.ofComplex_apply_of_im_pos hpos] at hm
  change Sum.inl (proj τ)∈Sum.inl ''(chartAt ℂ y).source at hm
  obtain ⟨a,ha,he⟩ := hm
  have hs : proj τ∈(chartAt ℂ y).source := by
    have he' := Sum.inl.inj he
    rwa [he'] at ha
  change proj τ∈((hf.localInverseAt (r y)).trans UpperHalfPlane.ofComplex.symm).source at hs
  have hd := lpsGamma0_localInverse_differential_pullback N hN f (r y) τ hs.1
  have heq : (((lpsOriginalFilledInteriorChart N hN x).symm.trans
      (lpsOriginalFilledInteriorChart N hN y)) : ℂ→ℂ)=
      (fun w : ℂ => ((hf.localInverseAt (r y)) (proj (UpperHalfPlane.ofComplex w)) : ℂ)) := by
    funext w
    rw [OpenPartialHomeomorph.trans_apply,lpsOriginalFilledInteriorChart_symm]
    change ((chartAt ℂ y).lift_openEmbedding
      (lpsOriginalFilledTopology_interior_openEmbedding N)) (Sum.inl (proj (UpperHalfPlane.ofComplex w)))=_
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rfl
  dsimp only
  rw [heq]
  simp only [UpperHalfPlane.ofComplex_apply]
  simpa only [τ,UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using hd
end QEC.Coding.TannerLiftedProduct
