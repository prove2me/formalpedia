-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.vec_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:40.333929+00:00
-- url     : https://prove2.me/submissions/c99b046b-405d-456d-b876-febc2c6d6f7d

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
theorem _root_.solution (v : Fin D → ℂ) : v = ∑ i, v i • (Pi.single i 1 : Fin D → ℂ) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext k
  by_cases h : k = i
  · subst h; simp
  · simp [h]
end ReciprocityTheory.AnForm.A.TraceConjugationCover
