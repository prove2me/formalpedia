-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_fderiv2_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:54.518672+00:00
-- url     : https://prove2.me/submissions/b33bad8d-d633-4b7f-984c-230353ca6d2f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_one_add_one_le_inf
import Theorems.Thm_ReciprocityTheory_AnForm_A_hasDerivAt_line
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_convex


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
theorem _root_.solution {η : ℝ} (hη : 0 < η) (p a : ι → ℝ) :
    0 ≤ fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) p a a := by
  have hF := regMax_contDiff (ι := ι) hη
  have hder : ∀ s : ℝ, HasDerivAt (fun s : ℝ => regMax η (p + s • a))
      (fderiv ℝ (regMax (ι := ι) η) (p + s • a) a) s := fun s =>
    (hF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_line p a s)
  have hconv : ConvexOn ℝ Set.univ (fun s : ℝ => regMax η (p + s • a)) := by
    refine ⟨convex_univ, fun x _ y _ c d hc hd hcd => ?_⟩
    have e : p + (c • x + d • y) • a = c • (p + x • a) + d • (p + y • a) := by
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-p j) * hcd
    show regMax η (p + (c • x + d • y) • a) ≤ c • regMax η (p + x • a) + d • regMax η (p + y • a)
    rw [e]
    exact (regMax_convex η).2 (Set.mem_univ _) (Set.mem_univ _) hc hd hcd
  have hmono : Monotone (deriv fun s : ℝ => regMax η (p + s • a)) := by
    have := hconv.monotoneOn_deriv (fun x _ => (hder x).differentiableAt)
    exact fun x y hxy => this (Set.mem_univ x) (Set.mem_univ y) hxy
  have h0 := hmono.deriv_nonneg (x := 0)
  have e2 : deriv (fun s : ℝ => regMax η (p + s • a)) =
      fun s => fderiv ℝ (regMax (ι := ι) η) (p + s • a) a := funext fun s => (hder s).deriv
  rw [e2] at h0
  have h2 : HasDerivAt (fun s : ℝ => fderiv ℝ (regMax (ι := ι) η) (p + s • a) a)
      (fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) p a a) 0 := by
    have hd := (hF.fderiv_right (m := 1) one_add_one_le_inf).differentiable one_ne_zero p
    have := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line p a 0) (by simp)
    simpa using this.clm_apply (hasDerivAt_const (0 : ℝ) a)
  rwa [h2.deriv] at h0
end ReciprocityTheory.AnForm.A
