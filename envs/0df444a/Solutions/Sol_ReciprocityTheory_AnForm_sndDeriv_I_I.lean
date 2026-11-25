-- Prove2me | solution 1 for ReciprocityTheory.AnForm.sndDeriv_I_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:36.444214+00:00
-- url     : https://prove2.me/submissions/74571509-f202-429e-8d7f-eb703b0a4ae3

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
theorem _root_.solution {τ : (ι → ℂ) → (κ → ℂ)} {z : ι → ℂ} (hτ : AnalyticAt ℂ τ z) (a : ι → ℂ) :
    fderiv ℝ (fderiv ℝ τ) z (Complex.I • a) (Complex.I • a) = - fderiv ℝ (fderiv ℝ τ) z a a :=
  fderiv_fderiv_I_smul_I_smul_of_analyticAt hτ a
end ReciprocityTheory.AnForm
