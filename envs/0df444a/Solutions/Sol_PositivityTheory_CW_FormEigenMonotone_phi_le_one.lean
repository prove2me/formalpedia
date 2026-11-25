-- Prove2me | solution 1 for PositivityTheory.CW.FormEigenMonotone.phi_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:26:23.629187+00:00
-- url     : https://prove2.me/submissions/c02d33ab-b4e2-4580-8d2d-05ffa236ccb5

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
theorem _root_.solution {s : ℕ} {R x : ℝ} (hR : 0 < R) (hx : 0 ≤ x) : phiR s R x ≤ 1 := by
  unfold phiR
  apply max_le _ zero_le_one
  have h1 : (1:ℝ) ≤ (1+x)^s := one_le_pow₀ (by linarith)
  have h2 : ((1+x)^s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have h3 : 0 ≤ ((1+R)^s)⁻¹ := by positivity
  linarith
end PositivityTheory.CW.FormEigenMonotone
