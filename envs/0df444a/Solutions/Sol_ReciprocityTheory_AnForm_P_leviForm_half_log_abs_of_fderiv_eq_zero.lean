-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.leviForm_half_log_abs_of_fderiv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:33.634816+00:00
-- url     : https://prove2.me/submissions/fdd2f849-1e84-4fdb-b6e7-9dac13972ee5

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Filter Topology Polynomial Matrix
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution {ι : Type} [Fintype ι] (f : (ι → ℂ) → ℝ) (z : ι → ℂ)
    (hf : ContDiffAt ℝ 2 f z) (hz : f z ≠ 0) (hd : fderiv ℝ f z = 0) (w : ι → ℂ) :
    levi (fun x => (1 / 2) * Real.log |f x|) z w = levi f z w / (2 * f z) := by
  have hev1 : ∀ᶠ x in 𝓝 z, f x ≠ 0 := hf.continuousAt.eventually_ne hz
  have hev2 : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 2 f x := hf.eventually (by simp)

  have hderiv : fderiv ℝ (fun x => (1 / 2) * Real.log |f x|) =ᶠ[𝓝 z]
      fun x => ((1 / 2) * (f x)⁻¹) • fderiv ℝ f x := by
    filter_upwards [hev1, hev2] with x hx1 hx2
    have hfd : HasFDerivAt f (fderiv ℝ f x) x := (hx2.differentiableAt (by norm_num)).hasFDerivAt
    have hl : HasFDerivAt (fun y => (1 / 2 : ℝ) * Real.log (f y)) ((1 / 2 : ℝ) • (f x)⁻¹ • fderiv ℝ f x) x :=
      (hfd.log hx1).const_mul (1 / 2)
    have e : (fun y => (1 / 2 : ℝ) * Real.log |f y|) = fun y => (1 / 2 : ℝ) * Real.log (f y) := by
      funext y
      rw [Real.log_abs]
    rw [e, hl.fderiv, smul_smul]
  have hL : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hfz : HasFDerivAt f (fderiv ℝ f z) z := (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasFDerivAt (fun x => (1 / 2 : ℝ) * (f x)⁻¹) _ z :=
    ((hasDerivAt_inv hz).comp_hasFDerivAt z hfz).const_mul (1 / 2 : ℝ)
  have hprod := hc.smul hL
  unfold levi
  have hprod' : HasFDerivAt (fun x => ((1 / 2 : ℝ) * (f x)⁻¹) • fderiv ℝ f x) _ z := hprod
  rw [hderiv.fderiv_eq, hprod'.fderiv, hd]
  simp
  field_simp
end ReciprocityTheory.AnForm.P
