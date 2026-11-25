-- Prove2me | solution 1 for PositivityTheory.CW.HilbertSchmidtNorm.L1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:22:29.984121+00:00
-- url     : https://prove2.me/submissions/ec95c342-0820-40a7-ac73-f0da7db093be

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_SecondDerivativeHolds

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
open PositivityTheory.CW.HilbertSchmidtNorm
variable {n : ℕ}
namespace PositivityTheory.CW.HilbertSchmidtNorm
theorem _root_.solution (r : ℕ) (u : ℝ) (hu : 1 ≤ u) :
    ((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * u ^ 2 ≤ r * u ^ r := by
  rcases r with _ | _ | k
  · simp
  · simp; linarith
  · have e1 : k + 1 + 1 - 1 = k + 1 := by omega
    have e2 : u ^ k * u ^ 2 = u ^ (k + 1 + 1) := by rw [← pow_add]
    rw [e1, mul_assoc, show k + 1 - 1 = k by omega, e2]
    have h0 : 0 ≤ u ^ (k + 1 + 1) := by positivity
    push_cast
    nlinarith
end PositivityTheory.CW.HilbertSchmidtNorm
