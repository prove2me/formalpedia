-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.levi_eq_lines
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:22.122863+00:00
-- url     : https://prove2.me/submissions/f4eb7043-732f-42c4-8da2-b2d59c582970

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Theorems.Thm_ReciprocityTheory_AnForm_P_deriv2_line

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
theorem _root_.solution {ι : Type*} [Fintype ι] {φ : (ι → ℂ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (w : ι → ℂ) :
    levi φ 0 w = (deriv (deriv (fun s : ℝ => φ (s • w))) 0 +
      deriv (deriv (fun s : ℝ => φ (s • (Complex.I • w)))) 0) / 4 := by
  unfold levi
  rw [deriv2_line hφ w, deriv2_line hφ (Complex.I • w)]
end ReciprocityTheory.AnForm.P
