-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsChowFormCycle_ne_zero_b5ee6986b005
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:32.994416+00:00
-- url     : https://prove2.me/submissions/992bcc16-2cd5-46b7-a215-1f26c005d3f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDefectAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory
namespace GroundTheory.Heights₂.Heights
namespace IsChowFormCycle
theorem _root_.solution {n k : ℕ} {Z : ProjCycle ℂ n} {f : MvPolynomial (Fin k × Fin n) ℂ}
    (hf : IsChowFormCycle Z k f) : f ≠ 0 := by
  obtain ⟨c, hc, g, hg, rfl⟩ := hf
  refine mul_ne_zero ?_ ?_
  · rw [Ne, MvPolynomial.C_eq_zero]; exact hc
  · rw [Finset.prod_ne_zero_iff]
    intro W hW
    exact pow_ne_zero _ (hg W hW).1
end IsChowFormCycle
end GroundTheory.Heights₂.Heights
