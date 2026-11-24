-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_InteriorDichotomy_proof_b0e821975e21
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:49:24.969847+00:00
-- url     : https://prove2.me/submissions/7a09efc5-a248-46ff-95bb-1de7d963efd2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PInteriorDichotomy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open Real
namespace GroundTheory.Heights₂.Heights.LowerBound
namespace InteriorDichotomy
theorem _root_.solution : InteriorDichotomy.Statement := by
  intro C0 C1 C2 hC0 hC1 hC2
  refine ⟨C0 * (log (3 + C2) + 2) + C1, ?_⟩
  intro h hmu g fj La H
  obtain ⟨hg, hfj, hgexp, hLa, hlow, hup⟩ := H
  have hLa0 : 0 < La := by linarith
  have hfj0 : 0 < fj := by linarith
  have hlog3 : 0 ≤ log (3 + C2) := Real.log_nonneg (by linarith)
  have hCnn : 0 ≤ C0 * (log (3 + C2) + 2) + C1 := by positivity
  by_cases hmu0 : 0 ≤ hmu
  · have : 0 ≤ (C0 * (log (3 + C2) + 2) + C1) * fj * La := by positivity
    linarith
  replace hmu0 : hmu < 0 := lt_of_not_ge hmu0

  have hgLa : 0 ≤ C2 * g * La := by positivity
  have hmax : max h 0 ≤ C2 * g * La := max_le (by linarith) hgLa
  have hpos : 0 < 2 + g + max h 0 := by have := le_max_right h 0; linarith
  have hgLa1 : 1 ≤ g * La := one_le_mul_of_one_le_of_one_le hg hLa
  have hstep1 : 2 + g + max h 0 ≤ (3 + C2) * (g * La) := by
    have : g ≤ g * La := le_mul_of_one_le_right (by linarith) hLa
    nlinarith
  have hLaexp : La ≤ exp La := by have := Real.add_one_le_exp La; linarith
  have hstep2 : g * La ≤ exp (2 * La) := by
    rw [show 2 * La = La + La by ring, Real.exp_add]
    exact mul_le_mul hgexp hLaexp hLa0.le (exp_pos La).le
  have hstep3 : 2 + g + max h 0 ≤ (3 + C2) * exp (2 * La) :=
    hstep1.trans (mul_le_mul_of_nonneg_left hstep2 (by linarith))
  have hlog : log (2 + g + max h 0) ≤ (log (3 + C2) + 2) * La := by
    calc log (2 + g + max h 0) ≤ log ((3 + C2) * exp (2 * La)) := Real.log_le_log hpos hstep3
      _ = log (3 + C2) + 2 * La := by
          rw [Real.log_mul (by linarith) (exp_pos _).ne', Real.log_exp]
      _ ≤ (log (3 + C2) + 2) * La := by nlinarith
  have hC0log : C0 * log (2 + g + max h 0) ≤ C0 * ((log (3 + C2) + 2) * La) :=
    mul_le_mul_of_nonneg_left hlog hC0
  have hin : C0 * log (2 + g + max h 0) + C1 * La ≤ (C0 * (log (3 + C2) + 2) + C1) * La := by
    nlinarith
  have := mul_le_mul_of_nonneg_left hin hfj0.le
  nlinarith
end InteriorDichotomy
end GroundTheory.Heights₂.Heights.LowerBound
