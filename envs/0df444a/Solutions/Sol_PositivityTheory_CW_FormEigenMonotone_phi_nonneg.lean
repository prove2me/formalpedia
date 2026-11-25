-- Prove2me | solution 1 for PositivityTheory.CW.FormEigenMonotone.phi_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:24:31.886102+00:00
-- url     : https://prove2.me/submissions/936210f6-0045-492a-9466-b7a204436d40

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisSumOfOrthogonality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.FormEigenMonotone
namespace PositivityTheory.CW.FormEigenMonotone
theorem _root_.solution (s : ℕ) (R x : ℝ) : 0 ≤ phiR s R x := le_max_right _ _
end PositivityTheory.CW.FormEigenMonotone
