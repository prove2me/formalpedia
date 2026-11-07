-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0Quotient_isManifold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:12.014758+00:00
-- url     : https://prove2.me/submissions/155e5c48-bc02-490b-b548-015c2911d6dd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Stabilizers
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Mathlib.Geometry.Manifold.Instances.Quotient
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Quotient
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_localInverse_analytic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Matrix Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsGamma0QuotientChartedSpace N hN
    IsManifold 𝓘(ℂ) ω (MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) := by
  let Q := MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
  let π : ℍ→Q := Quotient.mk _
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  have hp : Function.Surjective π := Quotient.mk_surjective
  let r := hp.hasRightInverse.choose
  let := lpsGamma0QuotientChartedSpace N hN
  apply isManifold_of_contDiffOn 𝓘(ℂ) ω Q
  intro a b ha hb
  change ∃ q, (hf.localInverseAt (r q)).trans (chartAt ℂ (r q))=a at ha
  change ∃ q, (hf.localInverseAt (r q)).trans (chartAt ℂ (r q))=b at hb
  obtain ⟨q,rfl⟩ := ha
  obtain ⟨q',rfl⟩ := hb
  have hc (τ : ℍ) : chartAt ℂ τ=UpperHalfPlane.ofComplex.symm := rfl
  simp only [hc]
  intro z hz
  have hpos : 0<z.im := by
    have hm := hz.1.1
    change z∈((hf.localInverseAt (r q)).trans UpperHalfPlane.ofComplex.symm).target at hm
    simpa [UpperHalfPlane.ofComplex] using hm.1
  let τ : ℍ := ⟨z,hpos⟩
  have hs : π τ∈(hf.localInverseAt (r q')).source := by
    have hm := hz.1.2
    change ((hf.localInverseAt (r q)).trans UpperHalfPlane.ofComplex.symm).symm z∈
      ((hf.localInverseAt (r q')).trans UpperHalfPlane.ofComplex.symm).source at hm
    simpa only [OpenPartialHomeomorph.trans_apply,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm,hf.localInverseAt_symm,
      UpperHalfPlane.ofComplex_apply_of_im_pos hpos,
      OpenPartialHomeomorph.symm_target] using hm.1
  have ht := lpsGamma0_localInverse_analytic N hN (r q') τ hs
  apply ContDiffAt.contDiffWithinAt
  simpa [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    OpenPartialHomeomorph.coe_trans,OpenPartialHomeomorph.coe_trans_symm,
    hf.localInverseAt_symm,UpperHalfPlane.ofComplex,Function.comp_def,τ,hf] using
    ht.contDiffAt (n:=ω)
end QEC.Coding.TannerLiftedProduct
