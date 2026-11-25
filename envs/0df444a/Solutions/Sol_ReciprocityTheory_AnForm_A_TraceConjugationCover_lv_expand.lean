-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.lv_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:41.659713+00:00
-- url     : https://prove2.me/submissions/12a07131-0ff9-4c08-a0a1-8d5293d5bb5b

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_lv_sum_left
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_lv_sum_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.TraceConjugationCover
open Complex Filter Topology Matrix
noncomputable section
variable {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
namespace ReciprocityTheory.AnForm.A.TraceConjugationCover
theorem _root_.solution (u v : Fin D → ℂ) :
    lv H u v = ∑ a, ∑ b, u a * lv H (Pi.single a 1) (Pi.single b 1) * starRingEnd ℂ (v b) := by
  rw [lv_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [lv_sum_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring
end ReciprocityTheory.AnForm.A.TraceConjugationCover
