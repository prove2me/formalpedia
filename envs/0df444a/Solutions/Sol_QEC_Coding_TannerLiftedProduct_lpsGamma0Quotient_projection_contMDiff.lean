-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0Quotient_projection_contMDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:13.133338+00:00
-- url     : https://prove2.me/submissions/92e8601c-d06b-4fdb-bfb1-97fbfc5ff366

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
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)) := by
  let Q := MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
  let π : ℍ→Q := Quotient.mk _
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  have hp : Function.Surjective π := Quotient.mk_surjective
  let r := hp.hasRightInverse.choose
  let := lpsGamma0QuotientChartedSpace N hN
  intro τ
  apply contMDiffAt_iff.mpr
  refine ⟨continuous_quot_mk.continuousAt,?_⟩
  have hs : π τ∈(hf.localInverseAt (r (π τ))).source := by
    have hc := ChartedSpace.mem_chart_source (H:=ℂ) (π τ)
    change π τ∈((hf.localInverseAt (r (π τ))).trans (chartAt ℂ (r (π τ)))).source at hc
    exact hc.1
  have ha := lpsGamma0_localInverse_analytic N hN (r (π τ)) τ hs
  have hc (z : ℍ) : chartAt ℂ z=UpperHalfPlane.ofComplex.symm := rfl
  have hchart : chartAt ℂ (π τ)=
      (hf.localInverseAt (r (π τ))).trans (chartAt ℂ (r (π τ))) := rfl
  simp only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,hc,Function.comp_id,Function.id_comp]
  simp [UpperHalfPlane.ofComplex]
  change ContDiffWithinAt ℂ ω
    (fun z : ℂ => chartAt ℂ (π τ) (π (UpperHalfPlane.ofComplex z))) Set.univ (τ:ℂ)
  rw [hchart]
  simpa [OpenPartialHomeomorph.trans_apply,UpperHalfPlane.ofComplex,Function.comp_def] using
    ha.contDiffAt (n:=ω) |>.contDiffWithinAt
end QEC.Coding.TannerLiftedProduct
