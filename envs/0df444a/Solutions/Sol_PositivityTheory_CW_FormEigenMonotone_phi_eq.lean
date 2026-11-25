-- Prove2me | solution 1 for PositivityTheory.CW.FormEigenMonotone.phi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:26:21.807313+00:00
-- url     : https://prove2.me/submissions/d466cb2b-0282-4409-ab80-1bbe07a714a1

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
theorem _root_.solution {s : ℕ} {R x : ℝ} (hx : 0 ≤ x) (hxR : x < R) :
    phiR s R x = ((1+x)^s)⁻¹ - ((1+R)^s)⁻¹ := by
  unfold phiR
  apply max_eq_left
  have h1 : (0:ℝ) < (1+x)^s := by positivity
  have h2 : (1+x)^s ≤ (1+R)^s := pow_le_pow_left₀ (by linarith) (by linarith) s
  have := inv_anti₀ h1 h2
  linarith
end PositivityTheory.CW.FormEigenMonotone
