-- Prove2me | solution 1 for PositivityTheory.KReal.GoodSideLattices.sd_sb_refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:37:32.281564+00:00
-- url     : https://prove2.me/submissions/e4964203-809a-4067-9381-1b4f52c2c319

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
theorem _root_.solution (a : Ix r s) : sameBlock a a := by
  rcases a with a | a <;> simp [sameBlock]
end PositivityTheory.KReal.GoodSideLattices
