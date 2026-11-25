-- Prove2me | solution 1 for PositivityTheory.KReal.CasGl.mul_Eab_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:00.440775+00:00
-- url     : https://prove2.me/submissions/51dd5fd5-60a1-4dff-98d2-c2f9ab41ddae

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCas
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
open PositivityTheory.KReal.CasGl
variable {r s : ℕ}
namespace PositivityTheory.KReal.CasGl
theorem _root_.solution (a b e f : Ix r s) (Z : Mat r s) :
    (Z * Eab a b) e f = if f = b then Z e a else 0 := by
  by_cases h : f = b
  · subst h; simp [Eab]
  · rw [if_neg h]; exact Matrix.mul_single_apply_of_ne _ _ _ _ _ h _
end PositivityTheory.KReal.CasGl
