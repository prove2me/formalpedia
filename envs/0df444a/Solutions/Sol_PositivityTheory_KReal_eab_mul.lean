-- Prove2me | solution 1 for PositivityTheory.KReal.eab_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:18.409518+00:00
-- url     : https://prove2.me/submissions/16d0d419-ae17-40ca-b5aa-6c4e03e708d3

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc

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
variable {r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution (a b c d : Ix r s) : Eab a b * Eab c d = if b = c then Eab a d else 0 := by
  unfold Eab
  split_ifs with h
  · subst h; simp
  · exact Matrix.single_mul_single_of_ne _ _ _ _ h _
end PositivityTheory.KReal
