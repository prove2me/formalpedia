-- Prove2me | solution 1 for PositivityTheory.KReal.CasGl.Eab_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:00:07.804796+00:00
-- url     : https://prove2.me/submissions/b43c2c0e-24a1-4298-9da8-2d378aa77a06

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
    (Eab a b * Z) e f = if e = a then Z b f else 0 := by
  by_cases h : e = a
  · subst h; simp [Eab]
  · rw [if_neg h]; exact Matrix.single_mul_apply_of_ne _ _ _ _ _ h _
end PositivityTheory.KReal.CasGl
