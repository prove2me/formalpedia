-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.fderiv_sum_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:00.686425+00:00
-- url     : https://prove2.me/submissions/0afac828-a5df-4eea-b5f3-c76b0d38a64c

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_sqForm_apply

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
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A.TraceConjugationCover
theorem _root_.solution :
    fderiv ℝ (fun w : Fin D → ℂ => ∑ i, Complex.normSq (w i)) =
      fun w => sqForm D w + (sqForm D).flip w := by
  have hf : (fun w : Fin D → ℂ => ∑ i, Complex.normSq (w i)) = fun w => sqForm D w w := by
    funext w
    rw [sqForm_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_self_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [hf]
  funext w
  have h : fderiv ℝ (fun y => sqForm D y y) w = _ :=
    ((sqForm D).hasFDerivAt_of_bilinear (hasFDerivAt_id w) (hasFDerivAt_id w)).fderiv
  rw [h]
  ext v
  simp [add_comm]
end ReciprocityTheory.AnForm.A.TraceConjugationCover
