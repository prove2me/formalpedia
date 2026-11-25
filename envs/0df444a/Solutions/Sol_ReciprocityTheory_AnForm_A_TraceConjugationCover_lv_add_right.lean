-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.lv_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:47.915455+00:00
-- url     : https://prove2.me/submissions/582f6cda-f4b8-40e3-ab4c-6de910859ca1

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
variable {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
namespace ReciprocityTheory.AnForm.A.TraceConjugationCover
theorem _root_.solution (a b b' : Fin D → ℂ) : lv H a (b + b') = lv H a b + lv H a b' := by
  simp only [lv, smul_add, map_add]
  push_cast
  ring
end ReciprocityTheory.AnForm.A.TraceConjugationCover
