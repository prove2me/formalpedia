-- Prove2me | solution 1 for PI.ExpIntWProof.keyW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:08:47.293975+00:00
-- url     : https://prove2.me/submissions/d590ef8e-9dea-4aad-bd61-009228ae7356

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
import Theorems.Thm_PI_ExpIntWProof_Key_isClosed_Wp
import Theorems.Thm_PI_ExpIntWProof_Key_natp_ne_zero
import Theorems.Thm_PI_ExpIntWProof_Key_div_p_mem_of_S

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof
open Key
namespace PI.ExpIntWProof
theorem _root_.solution : KeyW := by
  intro p _ x hx h
  rw [← SetLike.mem_coe, ← (isClosed_Wp p).closure_eq, Metric.mem_closure_iff]
  intro ε hε
  have hpn : (0 : ℝ) < ‖(p : ℂ_[p])‖ := norm_pos_iff.2 natp_ne_zero
  have hxS : x ∈ closure (S0 p : Set ℂ_[p]) := hx
  obtain ⟨y, hyS, hxy⟩ := Metric.mem_closure_iff.1 hxS (min (ε * ‖(p : ℂ_[p])‖) (1 - ‖x‖))
    (lt_min (mul_pos hε hpn) (by linarith))
  rw [dist_eq_norm] at hxy
  refine ⟨y / p, div_p_mem_of_S hyS ?_, ?_⟩
  · calc ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
      _ < ‖x‖ + (1 - ‖x‖) := by linarith [min_le_right (ε * ‖(p : ℂ_[p])‖) (1 - ‖x‖)]
      _ = 1 := by ring
  · rw [dist_eq_norm, ← sub_div, norm_div, div_lt_iff₀ hpn]
    exact lt_of_lt_of_le hxy (min_le_left _ _)
end PI.ExpIntWProof
