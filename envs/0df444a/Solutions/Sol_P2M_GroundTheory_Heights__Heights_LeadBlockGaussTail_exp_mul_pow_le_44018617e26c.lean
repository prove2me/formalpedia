-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_exp_mul_pow_le_44018617e26c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:02:37.094907+00:00
-- url     : https://prove2.me/submissions/6181a1e2-a40a-4465-af63-ef422dba90c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail

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
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail
namespace GroundTheory.Heights₂.Heights.LeadBlockGaussTail
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) {p : ℕ} (hp : p ≤ 1) :
    Real.exp (-t) * t ^ p ≤ 2 * Real.exp (-(t / 2)) := by
  have h1 := Real.add_one_le_exp (t / 2)
  have h2 : Real.exp (-t) = Real.exp (-(t / 2)) * Real.exp (-(t / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 := Real.exp_pos (-(t / 2))
  have h5 : Real.exp (-(t / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  interval_cases p
  · rw [pow_zero, mul_one, h2]; nlinarith
  · rw [pow_one, h2]; nlinarith [mul_pos h4 h4]
end GroundTheory.Heights₂.Heights.LeadBlockGaussTail
