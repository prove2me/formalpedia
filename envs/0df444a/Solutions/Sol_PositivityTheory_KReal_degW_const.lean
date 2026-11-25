-- Prove2me | solution 1 for PositivityTheory.KReal.degW_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:26.676036+00:00
-- url     : https://prove2.me/submissions/fde0c9c1-fdcb-4815-b6d1-d4f302a1ef89

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW

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
theorem _root_.solution {p q : ℕ} (c c0 : ℚ) :
    degW c (fun _ : Ix p q => c0) = p * |c0 - c| + q * |c0 + c| := by
  unfold degW
  simp [Fintype.sum_sum_type, shiftNu]
end PositivityTheory.KReal
