-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_cycleIntegral_eq_sum_9e1d366aec79
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:27.856995+00:00
-- url     : https://prove2.me/submissions/73be3bf8-532b-4475-a265-90d1933a54e0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PCycleIntegralSection

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
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (h : HermNorm n) (Z : ProjCycle ℂ n) (e : ℕ)
    (g : (Fin n → ℂ) → ℝ) :
    cycleIntegral h Z e g = Z.sum (fun W m => (m : ℝ) * coneIntegral h W e g) := rfl
end GroundTheory.Heights₂.Heights
