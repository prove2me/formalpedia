-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.smul_single_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:54.535348+00:00
-- url     : https://prove2.me/submissions/e74b9730-401b-48f2-8a03-defbcfbca47e

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt

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
theorem _root_.solution (i : Fin D) (c : ℂ) :
    c • (Pi.single i 1 : Fin D → ℂ) = Pi.single i c := by
  ext k
  by_cases h : k = i
  · subst h; simp
  · simp [h]
end ReciprocityTheory.AnForm.A.TraceConjugationCover
