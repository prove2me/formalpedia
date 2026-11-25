-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.sqForm_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:56.766205+00:00
-- url     : https://prove2.me/submissions/0d44dd18-7307-4832-90d1-f1b89531af79

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
theorem _root_.solution (i j : Fin D) (a b : ℂ) :
    sqForm D (Pi.single i a) (Pi.single j b) = if i = j then inner ℝ a b else 0 := by
  rw [sqForm_apply, Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst h; simp
    · simp [h, Pi.single_apply, Ne.symm h]
  · intro k _ hk; simp [hk]
  · simp
end ReciprocityTheory.AnForm.A.TraceConjugationCover
