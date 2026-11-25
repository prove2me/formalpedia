-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.contDiffOn_fubiniStudyProfileInv_normSqFirst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:25.09143+00:00
-- url     : https://prove2.me/submissions/c259d380-f2ff-4330-b7d2-f54cde97d40f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Theorems.Thm_ReciprocityTheory_AnForm_M_contDiff_fsQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => fubiniStudyProfileInv (fsQ w)) {w | w 0 ≠ 0} := by
  unfold fubiniStudyProfileInv
  have hne : ∀ w ∈ {w : Fin 1 → ℂ | w 0 ≠ 0}, fsQ w ≠ 0 := by
    intro w hw
    unfold fsQ
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  refine contDiffOn_const.mul ((contDiffOn_const.add (contDiff_fsQ.contDiffOn.inv hne)).log ?_)
  intro w hw
  have h0 : 0 ≤ (fsQ w)⁻¹ := by unfold fsQ; positivity
  show 1 + (fsQ w)⁻¹ ≠ 0
  exact ne_of_gt (by linarith)
end ReciprocityTheory.AnForm.M
