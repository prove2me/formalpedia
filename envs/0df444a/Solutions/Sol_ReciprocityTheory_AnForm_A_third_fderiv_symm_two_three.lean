-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.third_fderiv_symm_two_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:41.215196+00:00
-- url     : https://prove2.me/submissions/6c1976c7-7fbd-47dc-b52d-e55552015c15

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Theorems.Thm_ReciprocityTheory_AnForm_A_differentiableAt_snd_fderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (h : ContDiffAt ℝ 3 φ z)
    (u x y : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z u x y = fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z u y x := by
  have hd := differentiableAt_snd_fderiv φ z h
  have key : ∀ x y : Fin D → ℂ,
      fderiv ℝ (⇑(evalL x y) ∘ fderiv ℝ (fderiv ℝ φ)) z =
        (evalL x y).comp (fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z) :=
    fun x y => ((evalL x y).hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  have h2 : ContDiffAt ℝ 2 φ z := h.of_le (by first | norm_num | simp | rfl)
  have hev : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 φ w := h2.eventually (by first | simp | norm_num | decide | exact ENat.coe_ne_top _)
  have ev : (⇑(evalL x y) ∘ fderiv ℝ (fderiv ℝ φ)) =ᶠ[𝓝 z]
      (⇑(evalL y x) ∘ fderiv ℝ (fderiv ℝ φ)) := by
    filter_upwards [hev] with w hw
    simp only [Function.comp_apply, evalL, ContinuousLinearMap.coe_comp',
      ContinuousLinearMap.apply_apply]
    exact hw.isSymmSndFDerivAt (by first | simp | norm_num | (simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)) x y
  have e := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) ev
  rw [key x y, key y x] at e
  have e2 := congrArg (fun L => L u) e
  simpa only [evalL, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.apply_apply] using e2
end ReciprocityTheory.AnForm.A
