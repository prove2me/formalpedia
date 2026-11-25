-- Prove2me | solution 1 for PositivityTheory.KReal.GoodSideLattices.sd_trace_Eab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:31:16.06599+00:00
-- url     : https://prove2.me/submissions/75af3c6c-3074-4286-97ed-8d0c154ec133

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreStar
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGen
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSide

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
open PositivityTheory.KReal.GoodSideLattices
variable {p q r s : ℕ}
namespace PositivityTheory.KReal.GoodSideLattices
theorem _root_.solution (a b : Ix r s) : (Eab a b).trace = if a = b then 1 else 0 := by
  unfold Eab
  split_ifs with h
  · subst h
    simp [Matrix.trace]
  · simp [Matrix.trace, Matrix.single, h, Ne.symm h]
end PositivityTheory.KReal.GoodSideLattices
