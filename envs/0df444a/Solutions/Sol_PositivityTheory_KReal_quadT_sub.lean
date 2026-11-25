-- Prove2me | solution 1 for PositivityTheory.KReal.quadT_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:03.571845+00:00
-- url     : https://prove2.me/submissions/aa5cbdbc-8d51-451c-b408-dfa7f357c3ac

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie

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
variable {p q r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution {ι E : Type*} [Fintype ι] [Ring E] [Algebra ℂ E] (R L : ι → E) (A B : Matrix ι ι ℂ) :
    quadT R L (A - B) = quadT R L A - quadT R L B := by
  unfold quadT
  simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]
end PositivityTheory.KReal
