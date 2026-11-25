-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_comp_fderiv2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:51:21.630068+00:00
-- url     : https://prove2.me/submissions/a2ebfba7-8309-4950-894a-4efaed9d883a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_one_add_one_le_inf
import Theorems.Thm_ReciprocityTheory_AnForm_A_two_le_inf
import Theorems.Thm_ReciprocityTheory_AnForm_A_hasDerivAt_line_fderiv
import Theorems.Thm_ReciprocityTheory_AnForm_A_line_deriv_eventually
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv2_eq_deriv2
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_contDiff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {η : ℝ} (hη : 0 < η) {U : Set E} (hU : IsOpen U)
    {u : ι → E → ℝ} (hu : ∀ j, ContDiffOn ℝ 2 (u j) U) {z : E} (hz : z ∈ U) (v : E) :
    fderiv ℝ (fderiv ℝ (fun x => regMax η (fun j => u j x))) z v v =
      fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) (fun j => u j z) (fun j => fderiv ℝ (u j) z v)
          (fun j => fderiv ℝ (u j) z v) +
        fderiv ℝ (regMax (ι := ι) η) (fun j => u j z) (fun j => fderiv ℝ (fderiv ℝ (u j)) z v v) := by
  have hF : ContDiff ℝ ∞ (regMax (ι := ι) η) := regMax_contDiff hη
  have hG : ContDiffOn ℝ 2 (fun x => regMax η (fun j => u j x)) U :=
    (hF.of_le two_le_inf).comp_contDiffOn (contDiffOn_pi.2 hu)
  rw [fderiv2_eq_deriv2 hU hG hz v]
  have hγ : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s : ℝ => fun j => u j (z + s • v))
      (fun j => fderiv ℝ (u j) (z + s • v) v) s := by
    filter_upwards [Filter.eventually_all.2 fun j => line_deriv_eventually hU (hu j) hz v]
      with s hs
    exact hasDerivAt_pi.2 hs
  have e : deriv (fun s : ℝ => regMax η (fun j => u j (z + s • v))) =ᶠ[𝓝 0]
      fun s => fderiv ℝ (regMax (ι := ι) η) (fun j => u j (z + s • v))
        (fun j => fderiv ℝ (u j) (z + s • v) v) := by
    filter_upwards [hγ] with s hs
    exact ((hF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s hs).deriv
  rw [e.deriv_eq]
  have hA : HasDerivAt (fun s : ℝ => fderiv ℝ (regMax (ι := ι) η) (fun j => u j (z + s • v)))
      (fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) (fun j => u j z) (fun j => fderiv ℝ (u j) z v)) 0 := by
    have hγ0 : HasDerivAt (fun s : ℝ => fun j => u j (z + s • v))
        (fun j => fderiv ℝ (u j) z v) 0 := by
      have := hγ.self_of_nhds; simpa using this
    exact ((hF.fderiv_right (m := 1) one_add_one_le_inf).differentiable one_ne_zero
      (fun j => u j z)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ0 (by simp)
  have hB : HasDerivAt (fun s : ℝ => fun j => fderiv ℝ (u j) (z + s • v) v)
      (fun j => fderiv ℝ (fderiv ℝ (u j)) z v v) 0 :=
    hasDerivAt_pi.2 fun j => hasDerivAt_line_fderiv hU (hu j) hz v
  simpa using (hA.clm_apply hB).deriv
end ReciprocityTheory.AnForm.A
