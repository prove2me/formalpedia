-- Prove2me | solution 1 for PositivityTheory.CW.FormEigenMonotone.phi_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:45.538815+00:00
-- url     : https://prove2.me/submissions/56cfdb21-1ae5-4e73-817f-395d6ce8a248

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
theorem _root_.solution {s : ℕ} {R x : ℝ} (hR : 0 < R) (hx : R ≤ x) : phiR s R x = 0 := by
  unfold phiR
  apply max_eq_right
  have h1 : (0:ℝ) < (1+R)^s := by positivity
  have h2 : (1+R)^s ≤ (1+x)^s := pow_le_pow_left₀ (by linarith) (by linarith) s
  have := inv_anti₀ h1 h2
  linarith
end PositivityTheory.CW.FormEigenMonotone
