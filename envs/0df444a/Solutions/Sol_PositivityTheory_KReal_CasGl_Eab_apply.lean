-- Prove2me | solution 1 for PositivityTheory.KReal.CasGl.Eab_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:58:28.354487+00:00
-- url     : https://prove2.me/submissions/c0349bf4-754f-4c7b-8f79-f22feaffd45a

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
theorem _root_.solution (a b e f : Ix r s) : (Eab a b : Mat r s) e f = if a = e ∧ b = f then 1 else 0 := by
  simp [Eab, Matrix.single_apply]
end PositivityTheory.KReal.CasGl
