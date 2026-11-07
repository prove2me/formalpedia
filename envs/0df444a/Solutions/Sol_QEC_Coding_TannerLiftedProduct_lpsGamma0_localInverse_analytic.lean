-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0_localInverse_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:51:47.420614+00:00
-- url     : https://prove2.me/submissions/94d02d3e-be6f-4131-acdc-59612aa44f4d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Stabilizers
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Mathlib.Geometry.Manifold.Instances.Quotient
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Quotient
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_lifts_eventually_smul

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Matrix Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 4∣N)
    (σ τ : ℍ)
    (hs : Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ∈
      ((lpsGamma0_quotient_localHomeomorph N hN).localInverseAt σ).source) :
    AnalyticAt ℂ (fun z : ℂ =>
      (((lpsGamma0_quotient_localHomeomorph N hN).localInverseAt σ)
        (Quotient.mk (MulAction.orbitRel
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex z)) : ℂ)) τ := by
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  let e := hf.localInverseAt σ
  let π := Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
  let u : ℂ→ℍ := UpperHalfPlane.ofComplex
  let v : ℂ→ℍ := fun z => e (π (u z))
  have hu : ContinuousAt u (τ:ℂ) :=
    (UpperHalfPlane.contMDiffAt_ofComplex (n:=ω) τ.im_pos).continuousAt
  have hπ : Continuous π := continuous_quot_mk
  have ht : π (u τ)=π τ := by simp [u]
  have hv : ContinuousAt v (τ:ℂ) := by
    apply (e.continuousAt (by simpa only [ht] using hs)).comp
    exact hπ.continuousAt.comp hu
  have he : (fun z => π (v z)) =ᶠ[𝓝 (τ:ℂ)] (fun z => π (u z)) := by
    have hsrc : ∀ᶠ z in 𝓝 (τ:ℂ), π (u z)∈e.source := by
      apply hπ.continuousAt.comp hu
      change e.source∈𝓝 (π (u τ))
      exact e.open_source.mem_nhds (by simpa only [ht] using hs)
    filter_upwards [hsrc] with z hz
    exact hf.apply_localInverseAt_of_mem hz
  obtain ⟨γ,hγ⟩ := lpsGamma0_lifts_eventually_smul N hN u v τ hu hv he
  have hd : γ.val.val.det=1 := by
    obtain ⟨δ,hδ,hg⟩ := γ.property
    rw [←hg]
    simp only [← Matrix.GeneralLinearGroup.val_det_apply,Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have ha := UpperHalfPlane.analyticAt_smul (g:=γ.val) (by rw [hd];norm_num) τ
  apply ha.congr
  filter_upwards [hγ] with z hz
  exact congrArg UpperHalfPlane.coe hz.symm
end QEC.Coding.TannerLiftedProduct
