-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.sqForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:40.170794+00:00
-- url     : https://prove2.me/submissions/17f75beb-ad28-4444-8e5f-edd66368a163

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
theorem _root_.solution (v u : Fin D → ℂ) :
    sqForm D v u = ∑ i, inner ℝ (v i) (u i) := by
  simp [sqForm]
end ReciprocityTheory.AnForm.A.TraceConjugationCover
