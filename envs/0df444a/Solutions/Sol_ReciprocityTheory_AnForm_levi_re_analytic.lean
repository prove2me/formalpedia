-- Prove2me | solution 1 for ReciprocityTheory.AnForm.levi_re_analytic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:17.471846+00:00
-- url     : https://prove2.me/submissions/dcb781ab-2c41-4609-b209-6da8c1b6bb2a

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm
open Filter Topology
open scoped ContDiff
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
private theorem fderiv_fderiv_I_smul_I_smul_of_analyticAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {τ : E → F} {z : E}
    (hτ : AnalyticAt ℂ τ z) (a : E) :
    fderiv ℝ (fderiv ℝ τ) z (Complex.I • a) (Complex.I • a) = - fderiv ℝ (fderiv ℝ τ) z a a := by
  have hH : AnalyticAt ℂ (fderiv ℂ τ) z := hτ.fderiv
  let R := ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ

  have hev : fderiv ℝ τ =ᶠ[𝓝 z] fun y => R (fderiv ℂ τ y) := by
    filter_upwards [hτ.eventually_analyticAt] with y hy
    exact (hy.differentiableAt.hasFDerivAt.restrictScalars ℝ).fderiv
  have hD : HasFDerivAt (fun y => R (fderiv ℂ τ y))
      (R.comp ((fderiv ℂ (fderiv ℂ τ) z).restrictScalars ℝ)) z :=
    R.hasFDerivAt.comp z (hH.differentiableAt.hasFDerivAt.restrictScalars ℝ)
  rw [hev.fderiv_eq, hD.fderiv]
  simp [R, smul_smul]
end
end ReciprocityTheory.AnForm
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Filter Topology
open scoped ContDiff
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
namespace ReciprocityTheory.AnForm
theorem _root_.solution {G : (ι → ℂ) → ℂ} {z : ι → ℂ} (hG : AnalyticAt ℂ G z) (w : ι → ℂ) :
    levi (fun y => (G y).re) z w = 0 := by
  have hcd : ∀ n : ℕ∞, ContDiffAt ℝ n G z := fun n => (hG.contDiffAt (n := n)).restrict_scalars ℝ
  have hG1 : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ G y :=
    hG.eventually_analyticAt.mono fun y hy => hy.differentiableAt.restrictScalars ℝ
  let Q := ContinuousLinearMap.compL ℝ (ι → ℂ) ℂ ℝ Complex.reCLM
  have hev : fderiv ℝ (fun y => (G y).re) =ᶠ[𝓝 z] fun y => Q (fderiv ℝ G y) := by
    filter_upwards [hG1] with y hy
    exact ((Complex.reCLM.hasFDerivAt).comp y hy.hasFDerivAt).fderiv
  have hdG : DifferentiableAt ℝ (fderiv ℝ G) z :=
    ((hcd 2).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hD : HasFDerivAt (fun y => Q (fderiv ℝ G y)) (Q.comp (fderiv ℝ (fderiv ℝ G) z)) z :=
    Q.hasFDerivAt.comp z hdG.hasFDerivAt
  unfold levi
  rw [hev.fderiv_eq, hD.fderiv]
  have hI := fderiv_fderiv_I_smul_I_smul_of_analyticAt hG w
  simp only [ContinuousLinearMap.comp_apply, Q, ContinuousLinearMap.compL_apply,
    Complex.reCLM_apply, hI, Complex.neg_re]
  ring
end ReciprocityTheory.AnForm
