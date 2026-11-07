-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledInteriorChart_projection_differential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:08:33.97409+00:00
-- url     : https://prove2.me/submissions/bf34fa55-c866-4409-a037-6dfa0ca8aa52

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_localInverse_differential_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (τ : ℍ) (hs : letI := lpsOriginalFilledTopology N
      Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ)∈
        (lpsOriginalFilledInteriorChart N hN x).source) :
    letI := lpsOriginalFilledTopology N
    let Φ : ℂ→ℂ := fun z => lpsOriginalFilledInteriorChart N hN x
      (Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
        (UpperHalfPlane.ofComplex z)))
    f (UpperHalfPlane.ofComplex (Φ τ)) * deriv Φ τ = f τ := by
  let := lpsOriginalFilledTopology N
  let := lpsGamma0QuotientChartedSpace N hN
  let proj := Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  have hp : Function.Surjective proj := Quotient.mk_surjective
  let r := hp.hasRightInverse.choose
  change Sum.inl (proj τ)∈Sum.inl ''(chartAt ℂ x).source at hs
  obtain ⟨a,ha,he⟩ := hs
  have hm : proj τ∈(chartAt ℂ x).source := by
    have he' := Sum.inl.inj he
    rwa [he'] at ha
  change proj τ∈((hf.localInverseAt (r x)).trans UpperHalfPlane.ofComplex.symm).source at hm
  have hd := lpsGamma0_localInverse_differential_pullback N hN f (r x) τ hm.1
  have heq : (fun z : ℂ => lpsOriginalFilledInteriorChart N hN x
      (Sum.inl (proj (UpperHalfPlane.ofComplex z))))=
      (fun z : ℂ => ((hf.localInverseAt (r x)) (proj (UpperHalfPlane.ofComplex z)) : ℂ)) := by
    funext z
    change ((chartAt ℂ x).lift_openEmbedding (lpsOriginalFilledTopology_interior_openEmbedding N))
      (Sum.inl (proj (UpperHalfPlane.ofComplex z)))=_
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rfl
  dsimp only
  rw [heq]
  have he0 : lpsOriginalFilledInteriorChart N hN x (Sum.inl (proj τ))=
      ((hf.localInverseAt (r x)) (proj τ) : ℂ) := by
    simpa only [UpperHalfPlane.ofComplex_apply] using congrFun heq (τ:ℂ)
  simp only [UpperHalfPlane.ofComplex_apply]
  change f (UpperHalfPlane.ofComplex (lpsOriginalFilledInteriorChart N hN x (Sum.inl (proj τ)))) *
    deriv (fun z : ℂ => ((hf.localInverseAt (r x)) (proj (UpperHalfPlane.ofComplex z)) : ℂ)) τ = f τ
  rw [he0,UpperHalfPlane.ofComplex_apply]
  exact hd
end QEC.Coding.TannerLiftedProduct
