-- Prove2me | solution 1 for ReciprocityTheory.AnForm.levi_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:43.429458+00:00
-- url     : https://prove2.me/submissions/6d3c82ce-12bd-4bb3-9345-c0aba6777a5b

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Filter Topology
open scoped ContDiff
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
namespace ReciprocityTheory.AnForm
theorem _root_.solution {f g : (ι → ℂ) → ℝ} {z : ι → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) (w : ι → ℂ) :
    levi (fun y => f y + c * g y) z w = levi f z w + c * levi g z w := by
  have hf1 : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hg1 : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hev : fderiv ℝ (fun y => f y + c * g y) =ᶠ[𝓝 z]
      fun y => fderiv ℝ f y + c • fderiv ℝ g y := by
    filter_upwards [hf1, hg1] with y hfy hgy
    exact (hfy.hasFDerivAt.add (hgy.hasFDerivAt.const_mul c)).fderiv
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  unfold levi
  have hD : HasFDerivAt (fun y => fderiv ℝ f y + c • fderiv ℝ g y)
      (fderiv ℝ (fderiv ℝ f) z + c • fderiv ℝ (fderiv ℝ g) z) z :=
    hdf.hasFDerivAt.add (hdg.hasFDerivAt.const_smul c)
  rw [hev.fderiv_eq, hD.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
end ReciprocityTheory.AnForm
