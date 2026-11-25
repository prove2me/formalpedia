-- Prove2me | solution 1 for PositivityTheory.KReal.shiftNu_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:30:18.099295+00:00
-- url     : https://prove2.me/submissions/054ae02c-17e5-445c-b99c-999745bd605f

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreShape

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
namespace PositivityTheory.KReal
theorem _root_.solution {r s : ℕ} (c : ℚ) {μ ν : Ix r s → ℚ} (h : shiftNu c μ = shiftNu c ν) : μ = ν := by
  funext x
  have := congrFun h x
  rcases x with k | l <;> simp only [shiftNu] at this <;> linarith
end PositivityTheory.KReal
