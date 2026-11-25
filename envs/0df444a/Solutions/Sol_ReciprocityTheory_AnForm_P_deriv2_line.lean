-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.deriv2_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:09.8825+00:00
-- url     : https://prove2.me/submissions/d1fcb23a-861e-4ffa-a2ca-c29a67fad4c8

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Theorems.Thm_ReciprocityTheory_AnForm_P_hasDerivAt_line

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (v : E) :
    deriv (deriv (fun s : ℝ => φ (s • v))) 0 = fderiv ℝ (fderiv ℝ φ) 0 v v := by
  have hd : ∀ x, DifferentiableAt ℝ φ x := fun x => hφ.differentiable (by norm_num) x
  have e : deriv (fun s : ℝ => φ (s • v)) = fun s => fderiv ℝ φ (s • v) v := by
    funext s
    exact (hasDerivAt_line (hd _)).deriv
  rw [e]
  have hf2 : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : HasDerivAt (fun s : ℝ => s • v) v 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have h2 := (hf2 ((0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 := h2.clm_apply (hasDerivAt_const (0 : ℝ) v)
  rw [zero_smul] at h3
  simpa using h3.deriv
end ReciprocityTheory.AnForm.P
